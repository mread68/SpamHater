// SMTPCtrl.cpp

#include "SMTPApp.h"
#include <sqlext.h>
#include <crtdbg.h>
#include "SMTPCtrl.h"
#include "io.h"

//#define TESTING_DETAILED_LOGGING
//#define TESTING_PROCESS_LOGGING
//#define TESTING_RECV_LOGGING
//#define TESTING_ADDRESS_LOGGING
//#define TESTING_HEADER_LOGGING
//#define TESTING_MESSAGE_LOGGING
//#define TESTING_MESSAGE_LINE_LOGGING
//#define TESTING_MEMORY_LOGGING
//#define TESTING_INSTANT_LOGGING
//#define TESTING_USE_TEMP_FILE
//#define TESTING_FORCE_FULL_PROCESSING
//#define TESTING_KEEP_UNKNOWNS
//#define TESTING_EXTENDED_STATUS
//#define TESTING_FAKED_IP_ADDRESS
//#define TESTING_LOG_RAW_HTML_LINKS

#define DATABASE_STRUCTURE_ID		1
#define DATABASE_TYPE_ACCESS		0
#define DATABASE_TYPE_SQL			1
#define MEMORY_NEW_ALLOC

// Global Variables
extern BOOL					ServiceTerminating,ServicePaused,SharedThreads = TRUE;
static BOOL					ListenSocketClosed = FALSE,UpdateLog = TRUE,RejectIfFromInvalid = TRUE,RejectIfSameFromAndTo = TRUE,AcceptBlankMailFrom = TRUE,AcceptBlankBody = FALSE,ReverseResolution = TRUE,ForwardResolution = TRUE,ServiceOnHold = FALSE,OutbreakCheck = TRUE;
static int					ContextArraySize = 0,ThreadsToCreate,ThreadsCreated = 0,SocketTimeout = 120,SmartHostPort = 25,DeleteLogDays = 0,FormatErrors = BL_RESULT_FORWARD,RejectTagCount,EncodingLimit = 0,DNSBLSourceCount,DNSBLResultsCount,DNSBLAction = BL_RESULT_FORWARD,AlternateRouting = 0;
static CLIENT_CONTEXT		*ContextArray[MAX_CONTEXT+5];
static CRITICAL_SECTION		CriticalSection,KeywordCriticalSection,DomainCriticalSection,LocalCriticalSection,OutbreakCriticalSection,TrackingCriticalSection,MemoryCriticalSection,CommonFilesCriticalSection;
static __time64_t			LastFlushTime,LastConfigTime,TimeStarted;
static DWORD				TotalProcessTime = 0,MaxProcessTime = 0,MinProcessTime = 0,MaxProcessSize = 0,MinProcessSize = 0;
static char					*SMTPLog = NULL,MimecLookup64[64],MimecLookup32[32],MimecLookup16[16],*RejectTagsPtr[MAX_REJECT_TAGS],*DNSBLSourcePtr[MAX_DNSBL_SOURCES],*DNSBLResultsPtr[MAX_DNSBL_SOURCES];
static long					NextConnectionID = 1,MaxMessageSize = 0,MaxLinkSize = 0,TotalMessages = 0,BlackListMessages = 0,WhiteListMessages = 0,DeniedConnections = 0,MessagesDeleted = 0,OutbreakCount = 0,MaxTrackingSize = 0,BlackListSub[BL_TOTAL_STATS][BL_TOTAL_SUB_STATS];
static CSMTPControl			*pThis = NULL;
static char					TempFilePath[MAX_PATH_SIZE],LogFilePath[MAX_PATH_SIZE],TurfDir[MAX_PATH_SIZE],RejectTags[MAX_KEYWORD_SIZE],DNSBLSource[MAX_KEYWORD_SIZE],DNSBLResults[MAX_KEYWORD_SIZE];
static char					SmartHost[MAX_KEYWORD_SIZE],ForwardingAddress[MAX_KEYWORD_SIZE],AdminAddress[MAX_KEYWORD_SIZE],ServiceName[128];
static char					KeywordList[MAX_PATH_SIZE],DomainList[MAX_PATH_SIZE],LocalDomains[MAX_PATH_SIZE],TrackingLogFile[MAX_PATH_SIZE];
static DWORD				KeywordModified = 0,DomainModified = 0,LocalModified = 0;
static BOOL					KeywordLoaded = FALSE,DomainLoaded = FALSE,LocalLoaded = FALSE;
static MEMORY_BLOCK			*MemoryBlocks = NULL;
static FILTER_ENTRY			*KeywordFilters = NULL,*DomainFilters = NULL,*LocalFilters = NULL,*OutbreakFilters = NULL,*TrackingLog = NULL;
static int					KeywordAccessCount = 0,DomainAccessCount = 0,LocalAccessCount = 0,PortNumber = 25,MaxClients = 8;
static char					*DatabaseConnection = "TurboReports Database",*BlankTagLine = "-";
static long					DatabaseStructureID,TrackingLogSize = 0,LastSavedTrackingLogSize = 0,OutbreakLogSize = 0,DatabaseType = DATABASE_TYPE_SQL;
static HANDLE				ThreadHandles[MAX_THREADS];
static _invalid_parameter_handler	OldHandler,NewHandler;

CSMTPControl::CSMTPControl() : CSMTPService("SpamHater")
{
}

BOOL CSMTPControl::OnInit()
{
	int			Loop;

	m_CompletionPort = NULL;
	ServiceOnHold = FALSE;
	strcpy_s(ServiceName,sizeof(ServiceName),m_szServiceName);
	if (!LoadConfiguration(TRUE))
	{
		DebugMsg("%s %s %s","SMTP","Proxy","Failed to load configuration");
		return(FALSE);
	}

	// Set the initial state
	InitializeCriticalSectionAndSpinCount(&CriticalSection,-4000);
	InitializeCriticalSectionAndSpinCount(&KeywordCriticalSection,-4000);
	InitializeCriticalSectionAndSpinCount(&DomainCriticalSection,-4000);
	InitializeCriticalSectionAndSpinCount(&LocalCriticalSection,-4000);
	InitializeCriticalSectionAndSpinCount(&OutbreakCriticalSection,-4000);
	InitializeCriticalSectionAndSpinCount(&TrackingCriticalSection,-4000);
	InitializeCriticalSectionAndSpinCount(&MemoryCriticalSection,-4000);
	InitializeCriticalSectionAndSpinCount(&CommonFilesCriticalSection,-4000);

	for (Loop = 0; Loop < MAX_THREADS; Loop++)
		ThreadHandles[Loop] = NULL;

	// Set invalid parameter handler
	NewHandler = InvalidParameterHandler;
	OldHandler = _set_invalid_parameter_handler(NewHandler);
	_CrtSetReportMode(_CRT_ASSERT,0);

	if (UpdateLog && SMTPLog == NULL)
	{
		SMTPLog = new char[MAX_LOG_BUFFER+1];
		if (SMTPLog == NULL)
		{
			DebugMsg("%s %s %s","SMTP","Proxy","Could not allocate log buffer");
			DeleteCriticalSection(&CriticalSection);
			DeleteCriticalSection(&KeywordCriticalSection);
			DeleteCriticalSection(&DomainCriticalSection);
			DeleteCriticalSection(&LocalCriticalSection);
			DeleteCriticalSection(&OutbreakCriticalSection);
			DeleteCriticalSection(&TrackingCriticalSection);
			DeleteCriticalSection(&MemoryCriticalSection);
			DeleteCriticalSection(&CommonFilesCriticalSection);
			return(FALSE);
		}
		else
			memset(SMTPLog,0,MAX_LOG_BUFFER+1);
	}
	_time64(&LastFlushTime);
	_time64(&LastConfigTime);
	_time64(&TimeStarted);
	ContextArraySize = 0;

	if (!InitializeSockets())
	{
		DebugMsg("%s %s %s","SMTP","Proxy","Could not initialize sockets");
		if (SMTPLog != NULL)
		{
			delete [] SMTPLog;
			SMTPLog = NULL;
		}
		DeleteCriticalSection(&CriticalSection);
		DeleteCriticalSection(&KeywordCriticalSection);
		DeleteCriticalSection(&DomainCriticalSection);
		DeleteCriticalSection(&LocalCriticalSection);
		DeleteCriticalSection(&OutbreakCriticalSection);
		DeleteCriticalSection(&TrackingCriticalSection);
		DeleteCriticalSection(&MemoryCriticalSection);
		DeleteCriticalSection(&CommonFilesCriticalSection);
		return(FALSE);
	}

	if (SharedThreads && !InitializeThreads())
	{
		DebugMsg("%s %s %s","SMTP","Proxy","Could not initialize worker threads");
		CloseSockets(FALSE);
		WSACleanup();
		if (SMTPLog != NULL)
		{
			delete [] SMTPLog;
			SMTPLog = NULL;
		}
		DeleteCriticalSection(&CriticalSection);
		DeleteCriticalSection(&KeywordCriticalSection);
		DeleteCriticalSection(&DomainCriticalSection);
		DeleteCriticalSection(&LocalCriticalSection);
		DeleteCriticalSection(&OutbreakCriticalSection);
		DeleteCriticalSection(&TrackingCriticalSection);
		DeleteCriticalSection(&MemoryCriticalSection);
		DeleteCriticalSection(&CommonFilesCriticalSection);
		return(FALSE);
	}

	MimeDecodePrepare();
	LoadLocalDomainsFile();
	LoadDomainFilterFile();
	LoadKeywordFilterFile();
	LoadTrackingLogFile(NULL);
	#ifdef _DEBUG
	DebugMsg("%s %s %s","SMTP","Proxy","Leaving CSMTPControl::OnInit()");
	#endif
	pThis = this;
	return(TRUE);
}

void CSMTPControl::Run()
{
	if (!ServiceTerminating)
	{
		#ifdef _DEBUG
		DebugMsg("%s %s %s","SMTP","Proxy","Service is running");
		#endif
		UpdateLogFile("SMTP","Proxy","Service is running");
		FlushLogBuffers();
		AcceptClients();
		while (!ServiceTerminating)
			Sleep(5000);
	}
	#ifdef _DEBUG
	DebugMsg("%s %s %s","SMTP","Proxy","Leaving CSMTPControl::Run()");
	#endif
}

void CSMTPControl::OnStop()
{
	static WSAOVERLAPPED	Overlapped;
	int						Loop;
	char					Buffer[MAX_WORK_BUFFER_SIZE];
	long					TimeDays,TimeHours,TimeMinutes;
	DWORD					DailyCount = 0;
	float					DaysRunning;
	__time64_t				TimeRunning;

	// Notify all connected users that the service is terminating and shut down
	#ifdef _DEBUG
	DebugMsg("%s %s %s","SMTP","Proxy","Closing resources and stopping service");
	#endif
	#ifdef TESTING_PROCESS_LOGGING
	UpdateLogFile("SMTP","Proxy","Closing resources and stopping service");
	#endif
	if (SharedThreads && m_CompletionPort != NULL && ThreadsCreated > 0)
		for (Loop = 0; Loop < ThreadsCreated; Loop++)
			PostQueuedCompletionStatus(m_CompletionPort,0,INVALID_SOCKET,&Overlapped);
	EnterCriticalSection(&CriticalSection);
	TimeDays = TotalProcessTime/8640000;
	TimeHours = (TotalProcessTime-(TimeDays*8640000))/360000;
	TimeMinutes = (TotalProcessTime-(TimeDays*8640000)-(TimeHours*360000))/6000;
	sprintf_s(Buffer,sizeof(Buffer),"Process Time DHM=%ld:%02d:%02d, Min=%4.2f, Max=%4.2f, Avr=%4.2f",TimeDays,TimeHours,TimeMinutes,((float) MinProcessTime)/100,((float) MaxProcessTime)/100,(TotalMessages > 0 ? (((float) TotalProcessTime)/TotalMessages)/100 : 0.0f));
	UpdateLogFile("SpamHater","-",Buffer);
	_time64(&TimeRunning);
	TimeRunning -= TimeStarted;
	TimeDays = (long) (TimeRunning/86400);
	TimeHours = (long) ((TimeRunning-(TimeDays*86400))/3600);
	TimeMinutes = (long) ((TimeRunning-(TimeDays*86400)-(TimeHours*3600))/60);
	DaysRunning = ((((((float) TimeDays*24)+TimeHours)*60)+TimeMinutes)/60)/24;
	if (DaysRunning > 0)
		DailyCount = (DWORD) (BlackListMessages/DaysRunning);
	else
		DailyCount = 0;
	sprintf_s(Buffer,sizeof(Buffer),"Running DHM=%ld:%02d:%02d, Min Size=%ld, Max Size=%ld, Daily BL=%ld",TimeDays,TimeHours,TimeMinutes,MinProcessSize,MaxProcessSize,DailyCount);
	UpdateLogFile("SpamHater","-",Buffer);
	sprintf_s(Buffer,sizeof(Buffer),"Total Messages=%ld, Black List=%ld (%4.2f), White List=%ld (%4.2f)",TotalMessages,BlackListMessages,(TotalMessages > 0 ? (((float) BlackListMessages)*100)/TotalMessages : 0.0f),WhiteListMessages,(TotalMessages > 0 ? (((float) WhiteListMessages)*100)/TotalMessages : 0.0f));
	UpdateLogFile("SpamHater","-",Buffer);
	sprintf_s(Buffer,sizeof(Buffer),"BL Type: IP=%ld (%4.2f), Conn=%ld, Dom=%ld, HTML=%ld, DNSBL=%ld",BlackListSub[BL_IP][BL_SUB_TOTAL],(BlackListMessages > 0 ? (((float) BlackListSub[BL_IP][BL_SUB_TOTAL])*100)/BlackListMessages : 0.0f),BlackListSub[BL_IP][BL_SUB_IP_CONNECT],BlackListSub[BL_IP][BL_SUB_IP_DOMAIN],BlackListSub[BL_IP][BL_SUB_IP_HTML],BlackListSub[BL_IP][BL_SUB_IP_DNSBL]);
	UpdateLogFile("SpamHater","-",Buffer);
	sprintf_s(Buffer,sizeof(Buffer),"    Domain =%ld (%4.2f), Address=%ld, Suspect=%ld, Reverse=%ld",BlackListSub[BL_DOMAIN][BL_SUB_TOTAL],(BlackListMessages > 0 ? (((float) BlackListSub[BL_DOMAIN][BL_SUB_TOTAL])*100)/BlackListMessages : 0.0f),BlackListSub[BL_DOMAIN][BL_SUB_DOMAIN_ADDRESS],BlackListSub[BL_DOMAIN][BL_SUB_DOMAIN_SUSPECT],BlackListSub[BL_DOMAIN][BL_SUB_DOMAIN_REVERSE]);
	UpdateLogFile("SpamHater","-",Buffer);
	sprintf_s(Buffer,sizeof(Buffer),"    Keyword=%ld (%4.2f), Subject=%ld, Body=%ld",BlackListSub[BL_KEYWORD][BL_SUB_TOTAL],(BlackListMessages > 0 ? (((float) BlackListSub[BL_KEYWORD][BL_SUB_TOTAL])*100)/BlackListMessages : 0.0f),BlackListSub[BL_KEYWORD][BL_SUB_KEYWORD_SUBJECT],BlackListSub[BL_KEYWORD][BL_SUB_KEYWORD_BODY]);
	UpdateLogFile("SpamHater","-",Buffer);
	sprintf_s(Buffer,sizeof(Buffer),"    Format =%ld (%4.2f), Address=%ld, Body=%ld",BlackListSub[BL_FORMAT][BL_SUB_TOTAL],(BlackListMessages > 0 ? (((float) BlackListSub[BL_FORMAT][BL_SUB_TOTAL])*100)/BlackListMessages : 0.0f),BlackListSub[BL_FORMAT][BL_SUB_FORMAT_FROM],BlackListSub[BL_FORMAT][BL_SUB_FORMAT_BODY]);
	UpdateLogFile("SpamHater","-",Buffer);
	sprintf_s(Buffer,sizeof(Buffer),"    Tag    =%ld (%4.2f), Header=%ld, Admin Command=%ld",BlackListSub[BL_TAG][BL_SUB_TOTAL],(BlackListMessages > 0 ? (((float) BlackListSub[BL_TAG][BL_SUB_TOTAL])*100)/BlackListMessages : 0.0f),BlackListSub[BL_TAG][BL_SUB_TAG_HEADER],BlackListSub[BL_TAG][BL_SUB_TAG_ADMIN]);
	UpdateLogFile("SpamHater","-",Buffer);
	sprintf_s(Buffer,sizeof(Buffer),"Denied Connections=%ld, Messages Deleted=%ld, Outbreak Messages=%ld",DeniedConnections,MessagesDeleted,OutbreakCount);
	UpdateLogFile("SpamHater","-",Buffer);
	sprintf_s(Buffer,sizeof(Buffer),"Tracking Log Size=%ld, Outbreak Log Size=%ld, Threads=%d/%d",TrackingLogSize,OutbreakLogSize,ThreadsCreated,ContextArraySize);
	UpdateLogFile("SpamHater","-",Buffer);
	LeaveCriticalSection(&CriticalSection);
	FlushLogBuffers();
	SaveTrackingLogFile(NULL);
	FlushLogBuffers();
	ServiceTerminating = TRUE;
	ServicePaused = FALSE;
	if (m_CompletionPort != NULL)
	{
		CloseHandle(m_CompletionPort);
		m_CompletionPort = NULL;
	}
	ListenSocketClosed = TRUE;
	::shutdown(m_Listener,SD_BOTH);
	if (SharedThreads && ThreadsCreated > 0)
		for (Loop = 0; Loop < ThreadsCreated; Loop++)
			if (ThreadHandles[Loop] != NULL)
			{
				CloseHandle(ThreadHandles[Loop]);
				ThreadHandles[Loop] = NULL;
			}
	CloseSockets(FALSE);
	::closesocket(m_Listener);
	FlushLogBuffers();
	WSACleanup();
	EmptyLocalDomainsFile();
	EmptyDomainFilterFile();
	EmptyKeywordFilterFile();
	EmptyOutbreakFile();
	EmptyTrackingLogFile();
	#ifdef _DEBUG
	DebugMsg("%s %s %s","SMTP","Proxy","Service stopped");
	#endif
	UpdateLogFile("SMTP","Proxy","Service stopped");
	if (SMTPLog != NULL)
	{
		delete [] SMTPLog;
		SMTPLog = NULL;
	}
	ReleaseAllMemory();
	DeleteCriticalSection(&CriticalSection);
	DeleteCriticalSection(&KeywordCriticalSection);
	DeleteCriticalSection(&DomainCriticalSection);
	DeleteCriticalSection(&LocalCriticalSection);
	DeleteCriticalSection(&OutbreakCriticalSection);
	DeleteCriticalSection(&TrackingCriticalSection);
	DeleteCriticalSection(&MemoryCriticalSection);
	DeleteCriticalSection(&CommonFilesCriticalSection);
}

void CSMTPControl::OnPause()
{
	#ifdef _DEBUG
	DebugMsg("%s %s %s","SMTP","Proxy","Pausing service");
	#endif
	UpdateLogFile("SMTP","Proxy","Pausing service");
	ServicePaused = TRUE;
}

void CSMTPControl::OnContinue()
{
	#ifdef _DEBUG
	DebugMsg("%s %s %s","SMTP","Proxy","Continuing service");
	#endif
	UpdateLogFile("SMTP","Proxy","Continuing service");
	ServicePaused = FALSE;
}

BOOL CSMTPControl::OnUserControl(DWORD dwOpcode)
{
	// Process user control requests
	switch (dwOpcode)
	{
		case SERVICE_CONTROL_USER+0:
										return(TRUE);
										break;
		default:
										break;
	}
	return(FALSE); // say not handled
}

BOOL CSMTPControl::InitializeSockets()
{
	WSADATA				wsaData;
	WORD				wVersionRequested;
	int					nResult;
	char				Buffer[MAX_WORK_BUFFER_SIZE];

	wVersionRequested = MAKEWORD(2,2);
	nResult = WSAStartup(wVersionRequested,&wsaData);
	if (nResult != 0)
	{
		DebugMsg("%s %s %s","SMTP","Proxy","Socket initialization failed");
		return(FALSE);
	}
	if (LOBYTE(wsaData.wVersion) != 2 || HIBYTE(wsaData.wVersion) != 2)
	{
		sprintf_s(Buffer,sizeof(Buffer),"WinSock DLL must be version 2.2 not version %d.%d",LOBYTE(wsaData.wVersion),HIBYTE(wsaData.wVersion));
		DebugMsg("%s %s %s","SMTP","Proxy",Buffer);
		CloseSockets(FALSE);
		WSACleanup();
		return(FALSE);
	}
	return(TRUE);
}

void CSMTPControl::CloseSockets(BOOL Graceful)
{
	int			Loop;
	__time64_t	CurrentTime;

	EnterCriticalSection(&CriticalSection);
	for (Loop = ContextArraySize-1; Loop >= 0; Loop--)
		if (ContextArray[Loop]->SocketOpen)
		{
			CloseClient(ContextArray[Loop],Graceful);
			_time64(&ContextArray[Loop]->LastAccess);
			ContextArray[Loop]->SafeToDelete = TRUE;
		}
	LeaveCriticalSection(&CriticalSection);
	while (ContextArraySize > 0)
	{
		_time64(&CurrentTime);
		if (ContextArray[0]->SafeToDelete)
		{
			if ((long) (CurrentTime-ContextArray[0]->LastAccess) >= 5 && ContextArray[0]->SendComplete)
				DeleteContext(ContextArray[0],Graceful);
			else if (!ContextArray[0]->SendComplete)
				_time64(&ContextArray[0]->LastAccess);
		}
		else
		{
			if (!ContextArray[0]->TerminationMessage && (long) (CurrentTime-ContextArray[0]->LastAccess) > (long) SocketTimeout)
			{
				UpdateLogFile(ContextArray[0]->AddressString,GetConnectionTag(ContextArray[0]),"Connection stuck and is being terminated");
				_time64(&ContextArray[0]->LastAccess);
				ContextArray[0]->TerminationMessage = TRUE;
				ContextArray[0]->SafeToDelete = TRUE;
			}
		}
		Sleep(100);
	}
}

BOOL CSMTPControl::InitializeThreads()
{
	DWORD					ThreadID;
	SYSTEM_INFO				SystemInfo;
	int						Loop,Loop2;
	BOOL					Result = TRUE;
	char					Buffer[BUFFER_SIZE];
	static WSAOVERLAPPED	Overlapped;

	// Determine how many processors are on the system
	GetSystemInfo(&SystemInfo);

	// Create worker threads that will service the actual overlapped I/O requests
	ThreadsToCreate = (SharedThreads ? (int) SystemInfo.dwNumberOfProcessors*2 : 1);
	if (ThreadsToCreate < MaxClients*2)
		ThreadsToCreate = MaxClients*2;
	if (ThreadsToCreate > MAX_THREADS)
		ThreadsToCreate = MAX_THREADS;
	sprintf_s(Buffer,sizeof(Buffer),"Creating %d worker threads",ThreadsToCreate);
	#ifdef _DEBUG
	DebugMsg("%s %s %s","SMTP","Proxy",Buffer);
	#endif
	UpdateLogFile("SMTP","Proxy",Buffer);
	m_CompletionPort = CreateIoCompletionPort(INVALID_HANDLE_VALUE,NULL,0,ThreadsToCreate+1);
	if (m_CompletionPort != NULL)
	{
		for (Loop = 0; Result && Loop < ThreadsToCreate; Loop++)
		{
			ThreadHandles[ThreadsCreated] = CreateThread(NULL,0,WorkerThread,(void *) m_CompletionPort,0,&ThreadID);
			if (ThreadHandles[ThreadsCreated] == NULL)
			{
				ServiceTerminating = TRUE;
				if (ThreadsCreated > 0)
					for (Loop2 = 0; Loop2 < ThreadsCreated; Loop2++)
						if (ThreadHandles[Loop] != NULL)
						{
							PostQueuedCompletionStatus(m_CompletionPort,0,INVALID_SOCKET,&Overlapped);
							CloseHandle(ThreadHandles[Loop]);
							ThreadHandles[Loop] = NULL;
						}
				CloseHandle(m_CompletionPort);
				m_CompletionPort = NULL;
				Result = FALSE;
			}
			else
				ThreadsCreated++;
		}
	}
	else
		Result = FALSE;
	return(Result);
}

BOOL CSMTPControl::InitializeThread(CLIENT_CONTEXT *lpClientContext)
{
	BOOL			Result = FALSE;

	// Create worker thread that will service the connection
	if (lpClientContext != NULL)
	{
		#ifdef _DEBUG
		DebugMsg("%s %s %s",lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Creating worker thread");
		#endif
		#ifdef TESTING_PROCESS_LOGGING
		UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Creating worker thread");
		#endif
		if (lpClientContext->SocketOpen && lpClientContext->ThreadHandle == NULL && !lpClientContext->ThreadStarted && !lpClientContext->SafeToDelete && !lpClientContext->Timeout && !lpClientContext->TerminationMessage)
		{
			lpClientContext->ThreadHandle = CreateThread(NULL,0,WorkerThread,(void *) lpClientContext,CREATE_SUSPENDED,&lpClientContext->ThreadID);
			if (lpClientContext->ThreadHandle != NULL)
			{
				Result = TRUE;
				EnterCriticalSection(&CriticalSection);
				ThreadsCreated++;
				LeaveCriticalSection(&CriticalSection);
			}
		}
	}
	return(Result);
}

void CSMTPControl::AcceptClients()
{
	SOCKET				Socket;
	SOCKADDR_IN			sin,ConnectingAddress;
	int					Error,Zero,Size,OpenClients,Loop,DupConnectionCount,Num1,Num2,Num3,Num4;
	BOOL				Result = FALSE,KeepAlive,DontLinger,AcceptConnection,HandOffResult;
	DWORD				IoResult;
	CLIENT_CONTEXT		*lpClientContext;
	char				Buffer[MAX_WORK_BUFFER_SIZE],IPString[MAX_WORK_BUFFER_SIZE],TimeString[MAX_WORK_BUFFER_SIZE];
	LINGER				lingerStruct;
	HANDLE				NewCompletionPort = NULL;
	FILTER_ENTRY		*FilterList;

    // Create a listening socket that we'll use to accept incoming conections
	#ifdef _DEBUG
	DebugMsg("%s %s %s","SMTP","Proxy","CSMTPControl::AcceptClients()");
	#endif
	ListenSocketClosed = FALSE;
	m_Listener = ::socket(AF_INET,SOCK_STREAM,0);
	if (m_Listener != INVALID_SOCKET)
	{
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Proxy","Accepting new clients");
		#endif
		Result = TRUE;
		sin.sin_family = AF_INET;
		sin.sin_port = ::htons(PortNumber);
		sin.sin_addr.s_addr = INADDR_ANY;

		Error = ::bind(m_Listener,(LPSOCKADDR) &sin,sizeof(sin));
		if (Error == SOCKET_ERROR)
		{
			DebugMsg("%s %s %s","SMTP","Proxy","Failed to bind listening socket");
			UpdateLogFile("SMTP","Proxy","Failed to bind listening socket");
			ListenSocketClosed = TRUE;
			::shutdown(m_Listener,SD_BOTH);
			::closesocket(m_Listener);
			Result = FALSE;
		}

		if (Result)
		{
			// Listen for incoming connections on the socket
			Error = ::listen(m_Listener,5);
			if (Error == SOCKET_ERROR)
			{
				DebugMsg("%s %s %s","SMTP","Proxy","Socket failed to listen to port");
				UpdateLogFile("SMTP","Proxy","Socket failed to listen to port");
				ListenSocketClosed = TRUE;
				::shutdown(m_Listener,SD_BOTH);
				::closesocket(m_Listener);
				Result = FALSE;
			}
		}

		while (!ListenSocketClosed && !ServiceTerminating)
		{
			#ifdef _DEBUG
			DebugMsg("%s %s %s","SMTP","Proxy","Waiting for new connection");
			#endif
			#ifdef TESTING_DETAILED_LOGGING
			UpdateLogFile("SMTP","Proxy","Waiting for new connection");
			#endif
			Result = TRUE;
			Size = sizeof(ConnectingAddress);
			Socket = ::accept(m_Listener,(SOCKADDR *) &ConnectingAddress,&Size);
			lpClientContext = NULL;
			memset(IPString,0,sizeof(IPString));
			if (ServiceTerminating || ListenSocketClosed)
			{
				Result = FALSE;
				UpdateLogFile("SMTP","-","Service not available");
				sprintf_s(Buffer,sizeof(Buffer),"421 Service not available\r\n");
				::send(Socket,Buffer,strlen(Buffer),0);
			}
			else if (Socket == INVALID_SOCKET)
			{
				DebugMsg("%s %s %s","SMTP","-","Socket failed to accept incomming connection");
				UpdateLogFile("SMTP","-","Socket failed to accept incomming connection");
			}
			else if (Result)
			{
				Num1 = (unsigned char) ((SOCKADDR *) &ConnectingAddress)->sa_data[2];
				Num2 = (unsigned char) ((SOCKADDR *) &ConnectingAddress)->sa_data[3];
				Num3 = (unsigned char) ((SOCKADDR *) &ConnectingAddress)->sa_data[4];
				Num4 = (unsigned char) ((SOCKADDR *) &ConnectingAddress)->sa_data[5];
				sprintf_s(IPString,sizeof(IPString),"%d.%d.%d.%d",Num1,Num2,Num3,Num4);
				#ifdef TESTING_PROCESS_LOGGING
				UpdateLogFile(IPString,"-","Accept started");
				#endif
				CheckSocketTimeouts();
				#ifdef TESTING_FAKED_IP_ADDRESS
				((SOCKADDR *) &ConnectingAddress)->sa_data[2] = (unsigned char) 200;
				((SOCKADDR *) &ConnectingAddress)->sa_data[3] = (unsigned char) 69;
				((SOCKADDR *) &ConnectingAddress)->sa_data[4] = (unsigned char) 49;
				((SOCKADDR *) &ConnectingAddress)->sa_data[5] = (unsigned char) 99;
				#endif

				// Check if service is on hold
				if (Result && ServiceOnHold && !LocalAddress("",IPString))
				{
					sprintf_s(Buffer,sizeof(Buffer),"Service is on hold.  Terminating new connection.");
					UpdateLogFile(IPString,"-",Buffer);
					sprintf_s(Buffer,sizeof(Buffer),"451 Service is on hold.  Please try again in a few minutes.\r\n");
					::send(Socket,Buffer,strlen(Buffer),0);
					::shutdown(Socket,SD_BOTH);
					::closesocket(Socket);
					Result = FALSE;
					continue;
				}

				// Check maximum connections allowed
				OpenClients = CurrentClients();
				if (Result && ((OpenClients > MaxClients && !LocalAddress("",IPString) && !WhiteListIP(IPString)) || ContextArraySize >= MAX_CONTEXT))
				{
					if (OpenClients > MaxClients)
					{
						sprintf_s(Buffer,sizeof(Buffer),"Max connections reached.  Terminating new connection.");
						#ifdef _DEBUG
						DebugMsg("%s %s %s",IPString,"-",Buffer);
						#endif
					}
					else if (ContextArraySize >= MAX_CONTEXT)
					{
						sprintf_s(Buffer,sizeof(Buffer),"Max context array elements reached.  Terminating new connection.");
						#ifdef _DEBUG
						DebugMsg("%s %s %s",IPString,"-",Buffer);
						#endif
					}
					UpdateLogFile(IPString,"-",Buffer);
					sprintf_s(Buffer,sizeof(Buffer),"451 Maximum connections reached.  Please try again in a few minutes.\r\n");
					::send(Socket,Buffer,strlen(Buffer),0);
					::shutdown(Socket,SD_BOTH);
					::closesocket(Socket);
					Result = FALSE;
					continue;
				}

				// Check for existence of prior connection from this address
				if (Result && ContextArraySize > 0 && !LocalAddress("",IPString))
				{
//					Result = ConvertIPString(IPString,&Num1,&Num2,&Num3,&Num4);
					EnterCriticalSection(&CriticalSection);
					DupConnectionCount = 0;
					for (Loop = 0; Result && Loop < ContextArraySize; Loop++)
						if (!ContextArray[Loop]->SafeToDelete && Num1 == (unsigned char) ContextArray[Loop]->ConnectionAddress.sa_data[2] && Num2 == (unsigned char) ContextArray[Loop]->ConnectionAddress.sa_data[3] && Num3 == (unsigned char) ContextArray[Loop]->ConnectionAddress.sa_data[4] && Num4 == (unsigned char) ContextArray[Loop]->ConnectionAddress.sa_data[5])
							DupConnectionCount++;
					LeaveCriticalSection(&CriticalSection);

					// Allow only two connections per IP address
					if (!Result || DupConnectionCount > 1)
					{
						#ifdef _DEBUG
						DebugMsg("%s %s %s",IPString,"-","Terminating duplicate connection");
						#endif
						UpdateLogFile(IPString,"-","Terminating duplicate connection");
						sprintf_s(Buffer,sizeof(Buffer),"451 Only one connection per IP address is allowed\r\n");
						::send(Socket,Buffer,strlen(Buffer),0);
						::shutdown(Socket,SD_BOTH);
						::closesocket(Socket);
						Result = FALSE;
						continue;
					}
				}

				// Check IP address of connection
				if (Result)
				{
					AcceptConnection = TRUE;
//					AcceptConnection = ConvertIPString(IPString,&Num1,&Num2,&Num3,&Num4);
					if (AcceptConnection && DomainFilters != NULL)
					{
						EnterCriticalSection(&DomainCriticalSection);
						DomainAccessCount++;
						LeaveCriticalSection(&DomainCriticalSection);
						FilterList = DomainFilters;
						while (AcceptConnection && FilterList != NULL)
						{
							// Check only black listed IP addresses
							if ((FilterList->Filter[0] == '1' || FilterList->Filter[0] == '2') && FilterList->Filter[1] == '0' && FilterList->Filter[2] == '3')
								if (IPInSubnet((unsigned char) FilterList->Filter[4],(unsigned char) FilterList->Filter[5],(unsigned char) FilterList->Filter[6],(unsigned char) FilterList->Filter[7],(unsigned char) FilterList->Filter[8],(unsigned char) FilterList->Filter[9],(unsigned char) FilterList->Filter[10],(unsigned char) FilterList->Filter[11],Num1,Num2,Num3,Num4))
								{
									#ifdef _DEBUG
									DebugMsg("%s %s %s",IPString,"-","Connection denied");
									#endif
									EnterCriticalSection(&CriticalSection);
									DeniedConnections++;
									LeaveCriticalSection(&CriticalSection);
									UpdateLogFile(IPString,"-","Connection denied");
									sprintf_s(Buffer,sizeof(Buffer),"451 Connection denied\r\n");
									::send(Socket,Buffer,strlen(Buffer),0);
									::shutdown(Socket,SD_BOTH);
									::closesocket(Socket);
									Result = FALSE;
									AcceptConnection = FALSE;
								}
							FilterList = (FILTER_ENTRY *) FilterList->pvNext;
						}
						EnterCriticalSection(&DomainCriticalSection);
						DomainAccessCount--;
						LeaveCriticalSection(&DomainCriticalSection);
					}
				}

				// Create client context
				if (Result)
				{
					#ifdef TESTING_PROCESS_LOGGING
					UpdateLogFile(IPString,"-","Creating new client context");
					#endif
					lpClientContext = CreateContext(Socket,&ConnectingAddress);
					if (lpClientContext == NULL)
					{
						DebugMsg("%s %s %s",IPString,"-","Failed to allocate memory for new client context");
						UpdateLogFile(IPString,"-","Failed to allocate memory for new client context");
						sprintf_s(Buffer,sizeof(Buffer),"452 Local error in processing\r\n");
						::send(Socket,Buffer,strlen(Buffer),0);
						::shutdown(Socket,SD_BOTH);
						::closesocket(Socket);
						Result = FALSE;
						continue;
					}
					#ifdef _DEBUG
					DebugMsg("%s %s %s",IPString,"-","New connection accepted");
					#endif
					#ifdef TESTING_PROCESS_LOGGING
					sprintf_s(Buffer,sizeof(Buffer),"New connection accepted for ID %ld",lpClientContext->ConnectionID);
					UpdateLogFile(IPString,"-",Buffer);
					#endif
				}

				// Check access counts
				if (Result)
				{
					OpenClients = CurrentClients();
					EnterCriticalSection(&LocalCriticalSection);
					if (OpenClients == (!lpClientContext->SafeToDelete ? 1 : 0))
					{
						if (LocalAccessCount != 0)
						{
							UpdateLogFile("Reset","LocalAccessCount","to correct value");
							LocalAccessCount = 0;
						}
						if (DomainAccessCount != 0)
						{
							UpdateLogFile("Reset","DomainAccessCount","to correct value");
							DomainAccessCount = 0;
						}
						if (KeywordAccessCount != 0)
						{
							UpdateLogFile("Reset","KeywordAccessCount","to correct value");
							KeywordAccessCount = 0;
						}
					}
					LeaveCriticalSection(&LocalCriticalSection);
				}

				// Send welcome message
				if (Result && lpClientContext->SocketOpen)
				{
					sprintf_s(Buffer,sizeof(Buffer),"220 SpamHater ready at %s\r\n",BuildDateString(TimeString,sizeof(TimeString)));
					if ((Error = SendData(lpClientContext,Buffer,strlen(Buffer))) == SOCKET_ERROR)
					{
						if (lpClientContext->LastError != WSAECONNRESET && lpClientContext->LastError != 0)
							sprintf_s(Buffer,sizeof(Buffer),"Failed to send welcome message with WSA error %ld",(long) lpClientContext->LastError);
						else
							sprintf_s(Buffer,sizeof(Buffer),"Failed to send welcome message.  Connection was reset by client.");
						#ifdef _DEBUG
						DebugMsg("%s %s %s",IPString,"-",Buffer);
						#endif
						UpdateLogFile(IPString,"-",Buffer);
						CloseClient(lpClientContext,(Error == SOCKET_ERROR ? FALSE : TRUE));
						_time64(&lpClientContext->LastAccess);
						lpClientContext->SafeToDelete = TRUE;
						Result = FALSE;
						continue;
					}
				}

				if (Result && SharedThreads)
				{
					// Associate the new socket with a completion port.
					NewCompletionPort = CreateIoCompletionPort((HANDLE) Socket,m_CompletionPort,(DWORD) lpClientContext,ThreadsToCreate+1);
					if (NewCompletionPort == NULL)
					{
						#ifdef _DEBUG
						DebugMsg("%s %s %s",IPString,"-","Failed to associate completion port with connection");
						#endif
						UpdateLogFile(IPString,"-","Failed to associate completion port with connection");
						CloseClient(lpClientContext,TRUE);
						_time64(&lpClientContext->LastAccess);
						lpClientContext->SafeToDelete = TRUE;
					}
				}
			}
			if (Result && lpClientContext != NULL && lpClientContext->SocketOpen)
			{
				Zero = 0;
				KeepAlive = TRUE;
				lingerStruct.l_onoff = 1;
				lingerStruct.l_linger = 1;
				DontLinger = FALSE;
				Error = ::setsockopt(Socket,SOL_SOCKET,SO_SNDBUF,(char *) &Zero,sizeof(Zero));
				if (Error != SOCKET_ERROR)
					Error = ::setsockopt(Socket,SOL_SOCKET,SO_RCVBUF,(char *) &Zero,sizeof(Zero));
				if (Error != SOCKET_ERROR)
					Error = ::setsockopt(Socket,SOL_SOCKET,SO_KEEPALIVE,(char *) &KeepAlive,sizeof(KeepAlive));
				if (Error != SOCKET_ERROR)
					Error = ::setsockopt(Socket,SOL_SOCKET,SO_DONTLINGER,(char *) &DontLinger,sizeof(DontLinger));
				if (Error != SOCKET_ERROR)
					Error = ::setsockopt(Socket,SOL_SOCKET,SO_LINGER,(char *) &lingerStruct,sizeof(lingerStruct));
				if (Error == SOCKET_ERROR)
				{
					sprintf_s(Buffer,sizeof(Buffer),"Failed to set socket options on connection [%s]",lpClientContext->AddressString);
					#ifdef _DEBUG
					DebugMsg("%s %s %s",IPString,"-",Buffer);
					#endif
					UpdateLogFile(IPString,"-",Buffer);
					CloseClient(lpClientContext,FALSE);
					_time64(&lpClientContext->LastAccess);
					lpClientContext->SafeToDelete = TRUE;
				}
			}

			if (Result)
			{
				if (SharedThreads)
				{
					// Start an overlapped read on the socket.  This read will complete in one of the worker threads.
					#ifdef _DEBUG
					DebugMsg("%s %s %s",lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Handing off new connection to worker thread");
					#endif
					#ifdef TESTING_PROCESS_LOGGING
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Handing off new connection to worker thread");
					#endif
					memset(lpClientContext->Buffer,0,sizeof(lpClientContext->Buffer));
					HandOffResult = ReadFile((HANDLE) lpClientContext->Socket,lpClientContext->Buffer,(DWORD) sizeof(lpClientContext->Buffer),&IoResult,&lpClientContext->Overlapped);
					Error = (int) GetLastError();
					if (!HandOffResult && Error == ERROR_IO_PENDING)
					{
						// Still waiting for more data to be received from client but one of the threads will take it from here
					}
					else if (!HandOffResult && Error != ERROR_IO_PENDING)
					{
						#ifdef _DEBUG
						DebugMsg("%s %s %s",IPString,"-","Failed to read data from connection");
						#endif
						UpdateLogFile(IPString,"-","Failed to read data from connection");
						CloseClient(lpClientContext,FALSE);
						_time64(&lpClientContext->LastAccess);
						lpClientContext->SafeToDelete = TRUE;
					}
					#ifdef TESTING_PROCESS_LOGGING
					else if (HandOffResult)
					{
						sprintf_s(Buffer,sizeof(Buffer),"ReadFile() accepted %ld bytes for ID %ld",(long) IoResult,lpClientContext->ConnectionID);
						UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					}
					#endif
				}
				else if (lpClientContext != NULL && lpClientContext->SocketOpen)
				{
					// Create dedicated worker thread for new connection
					if (!InitializeThread(lpClientContext))
					{
						#ifdef _DEBUG
						DebugMsg("%s %s %s",IPString,"-","Failed to create thread");
						#endif
						UpdateLogFile(IPString,"-","Failed to create thread");
						CloseClient(lpClientContext,FALSE);
						_time64(&lpClientContext->LastAccess);
						lpClientContext->SafeToDelete = TRUE;
					}
					else
					{
						#ifdef TESTING_PROCESS_LOGGING
						UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Starting worker thread");
						#endif
						ResumeThread(lpClientContext->ThreadHandle);
						Sleep(100);
					}
				}
			}
			#ifdef TESTING_DETAILED_LOGGING
			if (Result && lpClientContext != NULL && lpClientContext->SocketOpen && lpClientContext->ThreadHandle != NULL)
				UpdateLogFile(IPString,"-","Accept complete");
			#endif
		}
	}
	#ifdef _DEBUG
	DebugMsg("%s %s %s","SMTP","Proxy","Leaving CSMTPControl::AcceptClients()");
	#endif
}

BOOL LoadConfiguration(BOOL FirstTimeLoad)
{
	HKEY				KeyHandle;
	char				KeyName[MAX_KEYWORD_SIZE];
	DWORD				Type,Size,Value;
	int					Loop,Loop2,MaxLength;
	BOOL				Result = TRUE;

	RejectTagCount = 0;
	DNSBLSourceCount = 0;
	DNSBLResultsCount = 0;
	for (Loop = 0; Loop < BL_TOTAL_STATS; Loop++)
		for (Loop2 = 0; Loop2 < BL_TOTAL_SUB_STATS; Loop2++)
			BlackListSub[Loop][Loop2] = 0;
	for (Loop = 0; Loop < MAX_REJECT_TAGS; Loop++)
		RejectTagsPtr[Loop] = NULL;
	for (Loop = 0; Loop < MAX_DNSBL_SOURCES; Loop++)
	{
		DNSBLSourcePtr[Loop] = NULL;
		DNSBLResultsPtr[Loop] = NULL;
	}
	memset(TempFilePath,0,sizeof(TempFilePath));
	memset(LogFilePath,0,sizeof(LogFilePath));
	memset(TurfDir,0,sizeof(TurfDir));
	memset(KeywordList,0,sizeof(KeywordList));
	memset(DomainList,0,sizeof(DomainList));
	memset(LocalDomains,0,sizeof(LocalDomains));
	memset(TrackingLogFile,0,sizeof(TrackingLogFile));
	memset(SmartHost,0,sizeof(SmartHost));
	memset(ForwardingAddress,0,sizeof(ForwardingAddress));
	memset(AdminAddress,0,sizeof(AdminAddress));
	memset(RejectTags,0,sizeof(RejectTags));
	memset(DNSBLSource,0,sizeof(DNSBLSource));
	memset(DNSBLResults,0,sizeof(DNSBLResults));

	// Read the registry parameters
	// HKEY_LOCAL_MACHINE\SYSTEM\CurrentControlSet\Services\<AppName>\Parameters
	strcpy_s(KeyName,sizeof(KeyName),"SYSTEM\\CurrentControlSet\\Services\\");
	strcat_s(KeyName,sizeof(KeyName),ServiceName);
	strcat_s(KeyName,sizeof(KeyName),"\\Parameters");
	if (RegOpenKeyEx(HKEY_LOCAL_MACHINE,KeyName,0,KEY_QUERY_VALUE,&KeyHandle) == ERROR_SUCCESS)
	{
		// Yes we are installed
		Type = REG_DWORD;
		Size = sizeof(Value);
		RegQueryValueEx(KeyHandle,"UpdateLog",NULL,&Type,(BYTE *) &Value,&Size);
		UpdateLog = (Value == 0 ? FALSE : TRUE);
		RegQueryValueEx(KeyHandle,"RejectIfFromInvalid",NULL,&Type,(BYTE *) &Value,&Size);
		RejectIfFromInvalid = (Value == 0 ? FALSE : TRUE);
		RegQueryValueEx(KeyHandle,"RejectIfSameFromAndTo",NULL,&Type,(BYTE *) &Value,&Size);
		RejectIfSameFromAndTo = (Value == 0 ? FALSE : TRUE);
		RegQueryValueEx(KeyHandle,"AcceptBlankMailFrom",NULL,&Type,(BYTE *) &Value,&Size);
		AcceptBlankMailFrom = (Value == 0 ? FALSE : TRUE);
		RegQueryValueEx(KeyHandle,"AcceptBlankBody",NULL,&Type,(BYTE *) &Value,&Size);
		AcceptBlankBody = (Value == 0 ? FALSE : TRUE);
		RegQueryValueEx(KeyHandle,"ReverseResolution",NULL,&Type,(BYTE *) &Value,&Size);
		ReverseResolution = (Value == 0 ? FALSE : TRUE);
		RegQueryValueEx(KeyHandle,"OutbreakCheck",NULL,&Type,(BYTE *) &Value,&Size);
		OutbreakCheck = (Value == 0 ? FALSE : TRUE);
		RegQueryValueEx(KeyHandle,"ForwardResolution",NULL,&Type,(BYTE *) &Value,&Size);
		ForwardResolution = (Value == 0 ? FALSE : TRUE);
		RegQueryValueEx(KeyHandle,"SocketTimeout",NULL,&Type,(BYTE *) &Value,&Size);
		SocketTimeout = Value;
		if (SocketTimeout < 10)
			SocketTimeout = 120;
		RegQueryValueEx(KeyHandle,"MaxMessageSize",NULL,&Type,(BYTE *) &Value,&Size);
		MaxMessageSize = Value;
		if (MaxMessageSize < 0)
			MaxMessageSize = 0;
		RegQueryValueEx(KeyHandle,"MaxTrackingSize",NULL,&Type,(BYTE *) &Value,&Size);
		MaxTrackingSize = Value;
		if (MaxTrackingSize < 1000)
			MaxTrackingSize = 95000;
		RegQueryValueEx(KeyHandle,"MaxLinkSize",NULL,&Type,(BYTE *) &Value,&Size);
		MaxLinkSize = Value;
		if (MaxLinkSize < 0)
			MaxLinkSize = 0;
		RegQueryValueEx(KeyHandle,"SmartHostPort",NULL,&Type,(BYTE *) &Value,&Size);
		SmartHostPort = Value;
		if (SmartHostPort <= 0)
			SmartHostPort = 25;
		RegQueryValueEx(KeyHandle,"EncodingLimit",NULL,&Type,(BYTE *) &Value,&Size);
		EncodingLimit = Value;
		if (EncodingLimit < 0)
			EncodingLimit = 0;
		RegQueryValueEx(KeyHandle,"DeleteLogDays",NULL,&Type,(BYTE *) &Value,&Size);
		DeleteLogDays = Value;
		if (DeleteLogDays <= 0)
			DeleteLogDays = 0;
		RegQueryValueEx(KeyHandle,"AlternateRouting",NULL,&Type,(BYTE *) &Value,&Size);
		AlternateRouting = Value;
		if (AlternateRouting <= 0)
			AlternateRouting = 0;
		RegQueryValueEx(KeyHandle,"FormatErrors",NULL,&Type,(BYTE *) &Value,&Size);
		FormatErrors = Value;
		if (FormatErrors != BL_RESULT_TURFDIR && FormatErrors != BL_RESULT_FORWARD && FormatErrors != BL_RESULT_DELETE)
			FormatErrors = BL_RESULT_FORWARD;
		RegQueryValueEx(KeyHandle,"DNSBLAction",NULL,&Type,(BYTE *) &Value,&Size);
		DNSBLAction = Value;
		if (DNSBLAction != BL_RESULT_TURFDIR && DNSBLAction != BL_RESULT_FORWARD && DNSBLAction != BL_RESULT_DELETE)
			DNSBLAction = BL_RESULT_FORWARD;
		if (FirstTimeLoad)
		{
			RegQueryValueEx(KeyHandle,"PortNumber",NULL,&Type,(BYTE *) &Value,&Size);
			PortNumber = Value;
			if (PortNumber <= 0)
				PortNumber = 25;
		}
		RegQueryValueEx(KeyHandle,"MaxClients",NULL,&Type,(BYTE *) &Value,&Size);
		MaxClients = Value;
		if (MaxClients > MAX_CONTEXT-5)
			MaxClients = MAX_CONTEXT-5;
		if (MaxClients <= 0)
			MaxClients = 8;
		Type = REG_SZ;
		Size = sizeof(TempFilePath)-1;
		RegQueryValueEx(KeyHandle,"TempFilePath",0,&Type,(BYTE *) TempFilePath,&Size);
		Size = sizeof(LogFilePath)-1;
		RegQueryValueEx(KeyHandle,"LogFilePath",0,&Type,(BYTE *) LogFilePath,&Size);
		Size = sizeof(TurfDir)-1;
		RegQueryValueEx(KeyHandle,"TurfDir",0,&Type,(BYTE *) TurfDir,&Size);
		Size = sizeof(KeywordList)-1;
		RegQueryValueEx(KeyHandle,"KeywordList",0,&Type,(BYTE *) KeywordList,&Size);
		Size = sizeof(DomainList)-1;
		RegQueryValueEx(KeyHandle,"DomainList",0,&Type,(BYTE *) DomainList,&Size);
		Size = sizeof(LocalDomains)-1;
		RegQueryValueEx(KeyHandle,"LocalDomains",0,&Type,(BYTE *) LocalDomains,&Size);
		Size = sizeof(TrackingLogFile)-1;
		RegQueryValueEx(KeyHandle,"TrackingLogFile",0,&Type,(BYTE *) TrackingLogFile,&Size);
		Size = sizeof(SmartHost)-1;
		RegQueryValueEx(KeyHandle,"SmartHost",0,&Type,(BYTE *) SmartHost,&Size);
		Size = sizeof(ForwardingAddress)-1;
		RegQueryValueEx(KeyHandle,"ForwardingAddress",0,&Type,(BYTE *) ForwardingAddress,&Size);
		Size = sizeof(AdminAddress)-1;
		RegQueryValueEx(KeyHandle,"AdminAddress",0,&Type,(BYTE *) AdminAddress,&Size);
		Size = sizeof(RejectTags)-1;
		RegQueryValueEx(KeyHandle,"RejectTags",0,&Type,(BYTE *) RejectTags,&Size);
		Size = sizeof(DNSBLSource)-1;
		RegQueryValueEx(KeyHandle,"DNSBLSource",0,&Type,(BYTE *) DNSBLSource,&Size);
		Size = sizeof(DNSBLResults)-1;
		RegQueryValueEx(KeyHandle,"DNSBLResults",0,&Type,(BYTE *) DNSBLResults,&Size);
		RegCloseKey(KeyHandle);
		if (strlen(AdminAddress) <= 0)
			strcpy_s(AdminAddress,sizeof(AdminAddress),ForwardingAddress);
		if (strlen(ForwardingAddress) <= 0)
			strcpy_s(ForwardingAddress,sizeof(ForwardingAddress),AdminAddress);
	}

	RejectTagCount = 0;
	MaxLength = (int) strlen(RejectTags);
	if (MaxLength > 0)
	{
		RejectTagsPtr[0] = RejectTags;
		RejectTagCount++;
	}
	Loop = 0;
	while (RejectTagCount < MAX_REJECT_TAGS && Loop < MaxLength)
	{
		if (RejectTags[Loop] == ';')
		{
			RejectTags[Loop] = '\0';
			RejectTagsPtr[RejectTagCount] = &RejectTags[Loop+1];
			RejectTagCount++;
		}
		Loop++;
	}

	DNSBLSourceCount = 0;
	MaxLength = (int) strlen(DNSBLSource);
	if (MaxLength > 0)
	{
		DNSBLSourcePtr[0] = DNSBLSource;
		DNSBLSourceCount++;
	}
	Loop = 0;
	while (DNSBLSourceCount < MAX_DNSBL_SOURCES && Loop < MaxLength)
	{
		if (DNSBLSource[Loop] == ';')
		{
			DNSBLSource[Loop] = '\0';
			DNSBLSourcePtr[DNSBLSourceCount] = &DNSBLSource[Loop+1];
			DNSBLSourceCount++;
		}
		Loop++;
	}

	DNSBLResultsCount = 0;
	MaxLength = (int) strlen(DNSBLResults);
	if (MaxLength > 0)
	{
		DNSBLResultsPtr[0] = DNSBLResults;
		DNSBLResultsCount++;
	}
	Loop = 0;
	while (DNSBLResultsCount < MAX_DNSBL_SOURCES && Loop < MaxLength)
	{
		if (DNSBLResults[Loop] == ';')
		{
			DNSBLResults[Loop] = '\0';
			DNSBLResultsPtr[DNSBLResultsCount] = &DNSBLResults[Loop+1];
			DNSBLResultsCount++;
		}
		Loop++;
	}
	return(Result);
}

void CheckSocketTimeouts()
{
	int			Loop,Error = SOCKET_ERROR;
	__time64_t	CurrentTime;
	char		Buffer[MAX_WORK_BUFFER_SIZE];

	#ifdef TESTING_PROCESS_LOGGING
	sprintf_s(Buffer,sizeof(Buffer),"Entering CheckSocketTimeouts(), Threads=%d/%d",ThreadsCreated,ContextArraySize);
	UpdateLogFile("SMTP","-",Buffer);
	#endif
	EnterCriticalSection(&CriticalSection);
	for (Loop = ContextArraySize-1; Loop >= 0; Loop--)
	{
		_time64(&CurrentTime);
		if (ContextArray[Loop]->SafeToDelete)
		{
			if ((long) (CurrentTime-ContextArray[Loop]->LastAccess) >= 5 && ContextArray[Loop]->SendComplete)
				DeleteContext(ContextArray[Loop],TRUE);
			else if (!ContextArray[Loop]->SendComplete)
				_time64(&ContextArray[Loop]->LastAccess);
		}
		else if ((long) (CurrentTime-ContextArray[Loop]->LastAccess) > (long) SocketTimeout && !ContextArray[Loop]->Timeout)
		{
			sprintf_s(Buffer,sizeof(Buffer),"Connection timeout for ID %ld",ContextArray[Loop]->ConnectionID);
			UpdateLogFile(ContextArray[Loop]->AddressString,GetConnectionTag(ContextArray[Loop]),Buffer);
			_time64(&ContextArray[Loop]->LastAccess);
			ContextArray[Loop]->Timeout = TRUE;
			if (ContextArray[Loop]->LastError == 0)
			{
				ContextArray[Loop]->LastError = SocketError(ContextArray[Loop]);
				CheckSocketError(ContextArray[Loop]);
				#ifdef TESTING_PROCESS_LOGGING
				sprintf_s(Buffer,sizeof(Buffer),"CheckSocketTimeouts() recorded socket error of %ld",(long) ContextArray[Loop]->LastError);
				UpdateLogFile(ContextArray[Loop]->AddressString,GetConnectionTag(ContextArray[Loop]),Buffer);
				#endif
			}
			CloseClient(ContextArray[Loop],FALSE);
		}
		else if (!ContextArray[Loop]->TerminationMessage && ContextArray[Loop]->Timeout && (long) (CurrentTime-ContextArray[Loop]->LastAccess) > (long) SocketTimeout && ContextArray[Loop]->CurrentState != STATE_DATA)
		{
			UpdateLogFile(ContextArray[Loop]->AddressString,GetConnectionTag(ContextArray[Loop]),"Connection stuck and is being terminated");
			_time64(&ContextArray[Loop]->LastAccess);
			ContextArray[Loop]->TerminationMessage = TRUE;
			ContextArray[Loop]->SafeToDelete = TRUE;
		}
	}
	LeaveCriticalSection(&CriticalSection);
	_time64(&CurrentTime);
	if ((long) (CurrentTime-LastFlushTime) > 60 || (SMTPLog != NULL && (long) strlen(SMTPLog) > (long) MAX_LOG_BUFFER-MAX_LOG_BUFFER_THRESHOLD))
		FlushLogBuffers();
	if ((long) (CurrentTime-LastConfigTime) > 20)
	{
		_time64(&LastConfigTime);
		LoadLocalDomainsFile();
		LoadDomainFilterFile();
		LoadKeywordFilterFile();
	}
}

int	CurrentClients()
{
	int		Loop,OpenClients = 0;

	EnterCriticalSection(&CriticalSection);
	for (Loop = ContextArraySize-1; Loop >= 0; Loop--)
		if (!ContextArray[Loop]->SafeToDelete)
			OpenClients++;
	LeaveCriticalSection(&CriticalSection);
	return(OpenClients);
}

CLIENT_CONTEXT *CreateContext(SOCKET Socket,SOCKADDR_IN *ConnectionAddress)
{
	CLIENT_CONTEXT	*lpClientContext = NULL;
	int				Loop,Num1,Num2,Num3,Num4;

	#ifdef TESTING_MEMORY_LOGGING
	{
		int Num1,Num2,Num3,Num4;
		char Buffer[MAX_WORK_BUFFER_SIZE];
		Num1 = (unsigned char) ((SOCKADDR *) &ConnectingAddress)->sa_data[2];
		Num2 = (unsigned char) ((SOCKADDR *) &ConnectingAddress)->sa_data[3];
		Num3 = (unsigned char) ((SOCKADDR *) &ConnectingAddress)->sa_data[4];
		Num4 = (unsigned char) ((SOCKADDR *) &ConnectingAddress)->sa_data[5];
		sprintf_s(Buffer,sizeof(Buffer),"%d.%d.%d.%d",Num1,Num2,Num3,Num4);
		UpdateLogFile(Buffer,"-","Allocating memory for new connection");
	}
	#endif
	if (ContextArraySize < MAX_CONTEXT+5)
	{
		#ifndef MEMORY_NEW_ALLOC
		lpClientContext = new CLIENT_CONTEXT;
		#else
		lpClientContext = (CLIENT_CONTEXT *) AllocateBlock(sizeof(CLIENT_CONTEXT),TRUE);
		#endif
		if (lpClientContext != NULL)
		{
			memset(lpClientContext,0,sizeof(CLIENT_CONTEXT));
			lpClientContext->SafeToDelete = FALSE;
			lpClientContext->Socket = Socket;
			lpClientContext->SocketOpen = TRUE;
			lpClientContext->HostSocket = INVALID_SOCKET;
			lpClientContext->HostSocketOpen = FALSE;
			lpClientContext->SendComplete = TRUE;
			lpClientContext->ProcessFilterExecuted = FALSE;
			lpClientContext->LastError = 0;
			lpClientContext->Overlapped.Internal = 0;
			lpClientContext->Overlapped.InternalHigh = 0;
			lpClientContext->Overlapped.Offset = 0;
			lpClientContext->Overlapped.OffsetHigh = 0;
			lpClientContext->Overlapped.hEvent = NULL;
			lpClientContext->ThreadID = 0;
			lpClientContext->ThreadHandle = NULL;
			lpClientContext->ThreadStarted = FALSE;
			lpClientContext->ThreadExited = FALSE;
			for (Loop = 0; Loop < COMMAND_MAX_RCPT; Loop++)
			{
				lpClientContext->RCPTcmd[Loop] = NULL;
				lpClientContext->RCPTcmdSize[Loop] = 0;
			}
			lpClientContext->RCPTCount = 0;
			lpClientContext->BufferPosition = 0;
			lpClientContext->FileOpen = FALSE;
			lpClientContext->TurfFileOpen = FALSE;
			lpClientContext->MessageSize = 0;
			lpClientContext->AllocatedSize = 0;
			lpClientContext->HTMLLinks = 0;
			lpClientContext->HTMLLinksResolved = 0;
			lpClientContext->ScanStep = 0;
			lpClientContext->ScanSize = 0;
			lpClientContext->ScanPosition = 0;
			lpClientContext->CharReplacements = 0;
			lpClientContext->HTMLAddrCount = 0;
			lpClientContext->ClientErrorCount = 0;
			lpClientContext->BlackListType = BL_NONE;
			lpClientContext->BlackListSubType = BL_SUB_TOTAL;
			lpClientContext->BlackListResult = FormatErrors;
			lpClientContext->WhiteRecipient = -1;
			lpClientContext->SuspectDomain = FALSE;
			lpClientContext->SuspectResult = FormatErrors;
			lpClientContext->WhiteList = FALSE;
			lpClientContext->PermBlackList = FALSE;
			lpClientContext->MessageBody = NULL;
			lpClientContext->MessageTruncated = FALSE;
			lpClientContext->MessageIncomplete = FALSE;
			lpClientContext->EmptyMessage = TRUE;
			lpClientContext->MultiPartMessage = FALSE;
			lpClientContext->Timeout = FALSE;
			lpClientContext->CurrentState = STATE_HELO;
			memset(lpClientContext->FileName,0,sizeof(lpClientContext->FileName));
			memset(lpClientContext->FullFileName,0,sizeof(lpClientContext->FullFileName));
			memset(lpClientContext->TurfFileName,0,sizeof(lpClientContext->TurfFileName));
			memset(lpClientContext->FilteredBy,0,sizeof(lpClientContext->FilteredBy));
			memset(lpClientContext->SubjectLine,0,sizeof(lpClientContext->SubjectLine));
			memset(lpClientContext->FromField,0,sizeof(lpClientContext->FromField));
			memset(lpClientContext->MessageID,0,sizeof(lpClientContext->MessageID));
			memset(lpClientContext->Boundary,0,sizeof(lpClientContext->Boundary));
			memset(lpClientContext->StepsTaken,0,sizeof(lpClientContext->StepsTaken));
			lpClientContext->CurrentBoundary = -1;
			lpClientContext->EndOfMessageBoundary = FALSE;
			lpClientContext->HELOAddress = NULL;
			memset(lpClientContext->HELOcmd,0,sizeof(lpClientContext->HELOcmd));
			memset(lpClientContext->MAILcmd,0,sizeof(lpClientContext->MAILcmd));
			memset(lpClientContext->MAILAddress,0,sizeof(lpClientContext->MAILAddress));
			lpClientContext->ForwardComplete = FALSE;
			lpClientContext->TerminationMessage = FALSE;
			memset(lpClientContext->AddressString,0,sizeof(lpClientContext->AddressString));
			memcpy(&lpClientContext->ConnectionAddress,ConnectionAddress,sizeof(SOCKADDR_IN));
			_time64(&lpClientContext->LastAccess);
			_ftime64_s(&lpClientContext->StartTime);
			_ftime64_s(&lpClientContext->EndTime);
			lpClientContext->TimeSpan = 0;
			lpClientContext->DatabaseConnected = FALSE;
			lpClientContext->DatabaseNativeError = 0;
			lpClientContext->StatementOpen = FALSE;
			lpClientContext->MessageIdentified = FALSE;
			memset(lpClientContext->DatabaseError,0,sizeof(lpClientContext->DatabaseError));
			memset(lpClientContext->DatabaseState,0,sizeof(lpClientContext->DatabaseState));
			Num1 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[2];
			Num2 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[3];
			Num3 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[4];
			Num4 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[5];
			sprintf_s(lpClientContext->AddressString,sizeof(lpClientContext->AddressString),"%d.%d.%d.%d",Num1,Num2,Num3,Num4);

			// Add new context to array but wait until array is not being edited by another process
			EnterCriticalSection(&CriticalSection);
			ContextArray[ContextArraySize] = lpClientContext;
			ContextArraySize++;
			lpClientContext->ConnectionID = NextConnectionID;
			NextConnectionID++;
			if (NextConnectionID >= 10000)
				NextConnectionID = 1;
			LeaveCriticalSection(&CriticalSection);
			#ifdef TESTING_MEMORY_LOGGING
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Memory allocated");
			#endif
		}
	}
	return(lpClientContext);
}

void DeleteContext(CLIENT_CONTEXT *lpClientContext,BOOL bGraceful)
{
	int		Loop,Loop2;
	char	Buffer[MAX_WORK_BUFFER_SIZE];

	if (lpClientContext != NULL)
		if (lpClientContext->SafeToDelete || lpClientContext->TerminationMessage)
		{
			// Delete context from array
			#ifdef _DEBUG
			if (pThis != NULL)
				pThis->DebugMsg("%s %s %s",lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Deleting client context");
			#endif
			#ifdef TESTING_PROCESS_LOGGING
			sprintf_s(Buffer,sizeof(Buffer),"Deleting client context for ID %ld",lpClientContext->ConnectionID);
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
			#endif
			if (!SharedThreads && lpClientContext->ThreadHandle == NULL && lpClientContext->ThreadStarted)
				UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Something wrong with memory context.  Memory leak.");
			if (SharedThreads)
			{
				if (lpClientContext->SocketOpen && lpClientContext->Socket != INVALID_SOCKET && !bGraceful)
				{
					#ifdef TESTING_PROCESS_LOGGING
					sprintf_s(Buffer,sizeof(Buffer),"DeleteContext() cancelling I/O on socket, currently %s",(lpClientContext->SendComplete ? "receiving" : "sending"));
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					#endif
					CancelIo((HANDLE) lpClientContext->Socket);
				}
				if (lpClientContext->HostSocketOpen && lpClientContext->HostSocket != INVALID_SOCKET)
				{
					#ifdef TESTING_PROCESS_LOGGING
					sprintf_s(Buffer,sizeof(Buffer),"DeleteContext() cancelling I/O on host socket, currently %s",(lpClientContext->SendComplete ? "receiving" : "sending"));
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					#endif
					CancelIo((HANDLE) lpClientContext->HostSocket);
				}
				Sleep(100);
			}
//			while (SharedThreads && bGraceful && !HasOverlappedIoCompleted(&lpClientContext->Overlapped))
//				Sleep(100);
			if (lpClientContext->SocketOpen)
				CloseClient(lpClientContext,bGraceful);
			if (!SharedThreads && lpClientContext->ThreadStarted)
			{
				if (lpClientContext->ThreadHandle != NULL)
				{
					if (!lpClientContext->ThreadExited)
					{
						_time64(&lpClientContext->LastAccess);
						lpClientContext->TerminationMessage = TRUE;
						lpClientContext->CurrentState = STATE_QUIT;
						Sleep(100);
						if (!lpClientContext->ThreadExited)
						{
							sprintf_s(Buffer,sizeof(Buffer),"Thread failed to terminate naturally with error %ld",(long) lpClientContext->LastError);
							UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
							#ifdef TESTING_DETAILED_LOGGING
							if (strlen(lpClientContext->Buffer) > 0 && strlen(lpClientContext->Buffer) < sizeof(lpClientContext->Buffer))
							{
								sprintf_s(Buffer,sizeof(Buffer),"First=%d, Buffer=%s",lpClientContext->Buffer[0],lpClientContext->Buffer);
								UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
							}
							#endif
							TerminateThread(lpClientContext->ThreadHandle,0);
						}
					}
					CloseHandle(lpClientContext->ThreadHandle);
				}
				lpClientContext->ThreadHandle = NULL;
				lpClientContext->ThreadStarted = FALSE;
				lpClientContext->ThreadExited = FALSE;
				EnterCriticalSection(&CriticalSection);
				ThreadsCreated--;
				LeaveCriticalSection(&CriticalSection);
			}
			EnterCriticalSection(&CriticalSection);
			for (Loop = 0; Loop < ContextArraySize; Loop++)
				if (ContextArray[Loop] == lpClientContext)
				{
					for (Loop2 = Loop; Loop2 < ContextArraySize-1; Loop2++)
						ContextArray[Loop2] = ContextArray[Loop2+1];
					ContextArraySize--;
				}
			LeaveCriticalSection(&CriticalSection);
			if (lpClientContext->MessageBody != NULL)
			{
				#ifndef MEMORY_NEW_ALLOC
				delete [] lpClientContext->MessageBody;
				#else
				ReleaseBlock((void *) lpClientContext->MessageBody,lpClientContext->AllocatedSize);
				#endif
				lpClientContext->MessageBody = NULL;
			}
			for (Loop = 0; Loop < COMMAND_MAX_RCPT; Loop++)
				if (lpClientContext->RCPTcmd[Loop] != NULL)
				{
					#ifndef MEMORY_NEW_ALLOC
					delete [] lpClientContext->RCPTcmd[Loop];
					#else
					ReleaseBlock((void *) lpClientContext->RCPTcmd[Loop],lpClientContext->RCPTcmdSize[Loop]);
					#endif
					lpClientContext->RCPTcmd[Loop] = NULL;
					lpClientContext->RCPTcmdSize[Loop] = 0;
				}
			lpClientContext->RCPTCount = 0;
			if (lpClientContext->FileOpen)
				fclose(lpClientContext->MessageFile);
			lpClientContext->FileOpen = FALSE;
			if (lpClientContext->TurfFileOpen)
				fclose(lpClientContext->TurfFile);
			lpClientContext->TurfFileOpen = FALSE;
			if (strlen(lpClientContext->FullFileName) > 0 && (lpClientContext->ForwardComplete || lpClientContext->MessageSize == 0))
				if (_access(lpClientContext->FullFileName,0) == 0)
					remove(lpClientContext->FullFileName);
			DisconnectFromDatabase(lpClientContext);
			#ifdef TESTING_PROCESS_LOGGING
			strcpy_s(Buffer,sizeof(Buffer),lpClientContext->AddressString);
			#endif
			#ifdef TESTING_MEMORY_LOGGING
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Cleared memory on connection");
			#endif
			#ifndef MEMORY_NEW_ALLOC
			delete lpClientContext;
			#else
			ReleaseBlock((void *) lpClientContext,sizeof(CLIENT_CONTEXT));
			#endif
			#ifdef TESTING_PROCESS_LOGGING
			sprintf_s(lpClientContext->AddressString,sizeof(lpClientContext->AddressString),"%s (deleted)",Buffer);
			#endif
		}
}

void ResetContext(CLIENT_CONTEXT *lpClientContext,BOOL ResetMailFrom)
{
	int		Loop;
	#ifdef TESTING_PROCESS_LOGGING
	char	Buffer[MAX_WORK_BUFFER_SIZE];
	#endif

	if (lpClientContext != NULL)
	{
		// Delete context from array but wait until array is not being edited by another process
		#ifdef _DEBUG
		if (pThis != NULL)
			pThis->DebugMsg("%s %s %s",lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Resetting client context");
		#endif
		#ifdef TESTING_PROCESS_LOGGING
		sprintf_s(Buffer,sizeof(Buffer),"Resetting client context for ID %ld",lpClientContext->ConnectionID);
		UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
		#endif
		if (lpClientContext->MessageBody != NULL)
		{
			#ifndef MEMORY_NEW_ALLOC
			delete [] lpClientContext->MessageBody;
			#else
			ReleaseBlock((void *) lpClientContext->MessageBody,lpClientContext->AllocatedSize);
			#endif
			lpClientContext->MessageBody = NULL;
		}
		lpClientContext->SafeToDelete = FALSE;
		for (Loop = 0; Loop < COMMAND_MAX_RCPT; Loop++)
			if (lpClientContext->RCPTcmd[Loop] != NULL)
			{
				#ifndef MEMORY_NEW_ALLOC
				delete [] lpClientContext->RCPTcmd[Loop];
				#else
				ReleaseBlock((void *) lpClientContext->RCPTcmd[Loop],lpClientContext->RCPTcmdSize[Loop]);
				#endif
				lpClientContext->RCPTcmd[Loop] = NULL;
				lpClientContext->RCPTcmdSize[Loop] = 0;
			}
		lpClientContext->RCPTCount = 0;
		if (lpClientContext->FileOpen)
			fclose(lpClientContext->MessageFile);
		lpClientContext->FileOpen = FALSE;
		if (lpClientContext->TurfFileOpen)
			fclose(lpClientContext->TurfFile);
		lpClientContext->TurfFileOpen = FALSE;
		if (strlen(lpClientContext->FullFileName) > 0 && (lpClientContext->ForwardComplete || lpClientContext->MessageSize == 0))
			if (_access(lpClientContext->FullFileName,0) == 0)
				remove(lpClientContext->FullFileName);
		if (lpClientContext->HostSocketOpen)
		{
			lpClientContext->HostSocketOpen = FALSE;
			if (lpClientContext->HostSocket != INVALID_SOCKET)
			{
				::shutdown(lpClientContext->HostSocket,SD_BOTH);
				::closesocket(lpClientContext->HostSocket);
				lpClientContext->HostSocket = INVALID_SOCKET;
			}
		}
		lpClientContext->SendComplete = TRUE;
		lpClientContext->ProcessFilterExecuted = FALSE;
		lpClientContext->BufferPosition = 0;
		lpClientContext->MessageSize = 0;
		lpClientContext->HTMLLinks = 0;
		lpClientContext->HTMLLinksResolved = 0;
		lpClientContext->ScanStep = 0;
		lpClientContext->ScanSize = 0;
		lpClientContext->ScanPosition = 0;
		lpClientContext->CharReplacements = 0;
		lpClientContext->HTMLAddrCount = 0;
		lpClientContext->ForwardComplete = FALSE;
		lpClientContext->TerminationMessage = FALSE;
		lpClientContext->BlackListType = BL_NONE;
		lpClientContext->BlackListSubType = BL_SUB_TOTAL;
		lpClientContext->BlackListResult = FormatErrors;
		lpClientContext->WhiteRecipient = -1;
		lpClientContext->SuspectDomain = FALSE;
		lpClientContext->SuspectResult = FormatErrors;
		lpClientContext->WhiteList = FALSE;
		lpClientContext->PermBlackList = FALSE;
		lpClientContext->MessageTruncated = FALSE;
		lpClientContext->MessageIncomplete = FALSE;
		lpClientContext->EmptyMessage = TRUE;
		lpClientContext->MultiPartMessage = FALSE;
		lpClientContext->Timeout = FALSE;
		lpClientContext->ConnectionID = 0;
		memset(lpClientContext->FileName,0,sizeof(lpClientContext->FileName));
		memset(lpClientContext->FullFileName,0,sizeof(lpClientContext->FullFileName));
		memset(lpClientContext->TurfFileName,0,sizeof(lpClientContext->TurfFileName));
		memset(lpClientContext->FilteredBy,0,sizeof(lpClientContext->FilteredBy));
		memset(lpClientContext->SubjectLine,0,sizeof(lpClientContext->SubjectLine));
		memset(lpClientContext->FromField,0,sizeof(lpClientContext->FromField));
		memset(lpClientContext->MessageID,0,sizeof(lpClientContext->MessageID));
		memset(lpClientContext->Boundary,0,sizeof(lpClientContext->Boundary));
		memset(lpClientContext->StepsTaken,0,sizeof(lpClientContext->StepsTaken));
		lpClientContext->CurrentBoundary = -1;
		lpClientContext->EndOfMessageBoundary = FALSE;
		_time64(&lpClientContext->LastAccess);
		_ftime64_s(&lpClientContext->StartTime);
		_ftime64_s(&lpClientContext->EndTime);
		lpClientContext->TimeSpan = 0;
		lpClientContext->DatabaseConnected = FALSE;
		lpClientContext->DatabaseNativeError = 0;
		lpClientContext->StatementOpen = FALSE;
		lpClientContext->MessageIdentified = FALSE;
		memset(lpClientContext->DatabaseError,0,sizeof(lpClientContext->DatabaseError));
		memset(lpClientContext->DatabaseState,0,sizeof(lpClientContext->DatabaseState));
		if (ResetMailFrom)
		{
			memset(lpClientContext->MAILcmd,0,sizeof(lpClientContext->MAILcmd));
			memset(lpClientContext->MAILAddress,0,sizeof(lpClientContext->MAILAddress));
		}
		DisconnectFromDatabase(lpClientContext);
	}
}

DWORD WINAPI WorkerThread(LPVOID WorkContext)
{
	HANDLE					CompletionPort = NULL;
	BOOL					FoundEndOfLine,QuitOnEndData = FALSE,ConfigLoaded,Result;//,OverlappedResult;
	DWORD					IoSize,IoResult,DailyCount = 0;
	float					DaysRunning;
	long					KillConnect,TimeDays,TimeHours,TimeMinutes,SizeParam;
	unsigned long			IoKey;
	LPWSAOVERLAPPED			lpOverlapped;
	CLIENT_CONTEXT			*lpClientContext = NULL;
	char					Buffer[MAX_WORK_BUFFER_SIZE],VRFYBuffer[COMMAND_VRFY_LEN+1],PercentString[10],*Pointer,*AltPointer,*CommandStart;
	int						Command,SecondCommand,Loop,Loop2,OpenClients,BufferSize,LastError,Num1,Num2,Num3,Num4;
	__time64_t				CurrentTime,TimeRunning;
	FILTER_ENTRY			*FilterList;
	SQLRETURN				ReturnCode;

	// SMTP Error Codes
	// 211 System status, or system help reply
	// 214 Help message
	// 220 Service ready
	// 221 Service closing transmission channel
	// 250 OK
	// 251 User not local; will forward to...
	// 354 Start mail input, end with <CRLF>.<CRLF>
	// 421 Service not available
	// 450 Requested action not taken: busy
	// 451 Requested action aborted
	// 452 Requested action not taken: insufficient system storage
	// 500 Unrecognized command
	// 501 Unrecognized parameter
	// 502 Command not implemented
	// 503 Bad command sequence
	// 504 Command parameter not implemented
	// 550 Unable to relay for...
	// 551 User not local; please try...
	// 552 Maximum message size exceeded
	// 553 Requested action not taken: mailbox name not allowed (e.g., mailbox syntax incorrect)
	// 554 Transaction failed
	if (SharedThreads)
		CompletionPort = (HANDLE) WorkContext;
	else
		lpClientContext = (CLIENT_CONTEXT *) WorkContext;
	if (!SharedThreads && lpClientContext != NULL)
	{
		lpClientContext->ThreadStarted = TRUE;
		lpClientContext->ThreadExited = FALSE;
		#ifdef TESTING_PROCESS_LOGGING
		UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Worker thread started");
		#endif
		_time64(&lpClientContext->LastAccess);
		memset(lpClientContext->Buffer,0,sizeof(lpClientContext->Buffer));
		lpClientContext->CurrentState = STATE_HELO;
		if (!lpClientContext->SocketOpen)
		{
			lpClientContext->CurrentState = STATE_QUIT;
			_time64(&lpClientContext->LastAccess);
			lpClientContext->SafeToDelete = TRUE;
		}
	}
	else if (SharedThreads && CompletionPort != NULL)
	{
		// Everything looks good
	}
	else if (!SharedThreads)
		return(0);
	while (TRUE)
	{
		if ((SharedThreads && CompletionPort != NULL) || (!SharedThreads && lpClientContext != NULL && lpClientContext->SocketOpen && !lpClientContext->SafeToDelete && !lpClientContext->Timeout && !lpClientContext->TerminationMessage))
		{
			if (SharedThreads)
			{
				IoSize = 0;
				if (lpClientContext != NULL)
				{
					// Make sure only one thread at a time processes each client context
					if (lpClientContext->CurrentState <= STATE_DATA || lpClientContext->SafeToDelete || lpClientContext->TerminationMessage)
						lpClientContext = NULL;
					else if (!lpClientContext->ProcessFilterExecuted)
					{
						// If the current state is passed receiving data but the scanning process hasn't started then wait for a moment
						Sleep(100);
						if (lpClientContext->ProcessFilterExecuted)
						{
							// This context has been taken by another thread so stop processing here
							lpClientContext = NULL;
						}
					}
					else
						lpClientContext = NULL;
				}
				if (lpClientContext == NULL)
				{
					Result = GetQueuedCompletionStatus(CompletionPort,&IoSize,&IoKey,&lpOverlapped,INFINITE);
					if ((long) IoKey != -1 && lpOverlapped != NULL)
					{
						lpClientContext = (CLIENT_CONTEXT *) IoKey;
						if (!lpClientContext->ThreadStarted)
						{
							lpClientContext->ThreadStarted = TRUE;
							lpClientContext->ThreadExited = FALSE;
							#ifdef TESTING_PROCESS_LOGGING
							sprintf_s(Buffer,sizeof(Buffer),"Worker thread accepting new handoff request for ID %ld",lpClientContext->ConnectionID);
							UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
							#endif
							_time64(&lpClientContext->LastAccess);
							lpClientContext->CurrentState = STATE_HELO;
							if (!lpClientContext->SocketOpen)
							{
								lpClientContext->CurrentState = STATE_QUIT;
								_time64(&lpClientContext->LastAccess);
								lpClientContext->SafeToDelete = TRUE;
							}
						}
					}
					if (lpClientContext == NULL)
						IoSize = -1;
					if ((long) IoSize < 0 || (lpClientContext != NULL && (long) IoSize == 1 && lpClientContext->Buffer[0] == '\x01'))
					{
						// Simulate connection reset if no data is received
						IoSize = -1;
						if (lpClientContext != NULL)
						{
							lpClientContext->LastError = WSAECONNRESET;
							sprintf_s(Buffer,sizeof(Buffer),"GetQueuedCompletionStatus() failed with simulated WSA error %ld for ID %ld",(long) lpClientContext->LastError,lpClientContext->ConnectionID);
							UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
							CloseClient(lpClientContext,FALSE);
						}
//						else
//							UpdateLogFile("SMTP","Proxy","GetQueuedCompletionStatus() failed");
					}
					else if ((long) IoSize >= 0 && lpClientContext != NULL)
					{
						// Accepted data on socket
						#ifdef TESTING_PROCESS_LOGGING
						sprintf_s(Buffer,sizeof(Buffer),"GetQueuedCompletionStatus() accepted %ld bytes for ID %ld",(long) IoSize,lpClientContext->ConnectionID);
						UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
						#endif
						if (IoSize == 0)
						{
							// There was a timeout, reset or some other problem on the socket so close it and continue with process
							lpClientContext->LastError = SocketError(lpClientContext);
							sprintf_s(Buffer,sizeof(Buffer),"Detecting error %ld on socket for ID %ld",(long) lpClientContext->LastError,lpClientContext->ConnectionID);
							UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
							CloseClient(lpClientContext,FALSE);
						}
					}
				}
			}
			else if (lpClientContext->SocketOpen && lpClientContext->ThreadHandle != NULL)
			{
				IoSize = 0;
				while (!ServiceTerminating && lpClientContext->SocketOpen && !lpClientContext->SafeToDelete && lpClientContext->CurrentState != STATE_QUIT && lpClientContext->ThreadHandle != NULL && !lpClientContext->Timeout && !lpClientContext->TerminationMessage && (long) IoSize == 0)
				{
					IoSize = ::recv(lpClientContext->Socket,&lpClientContext->Buffer[lpClientContext->BufferPosition],sizeof(lpClientContext->Buffer)-lpClientContext->BufferPosition-1,0);
					if ((long) IoSize > 0)
					{
						// Accepted data on socket
						#ifdef TESTING_PROCESS_LOGGING
						sprintf_s(Buffer,sizeof(Buffer),"Accepted %ld bytes for ID %ld",(long) IoSize,lpClientContext->ConnectionID);
						UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
						#endif
					}
					else if (!lpClientContext->Timeout && !lpClientContext->TerminationMessage)
					{
						// There was an error on the socket so close it
						if (lpClientContext->LastError == 0)
						{
							lpClientContext->LastError = SocketError(lpClientContext);
							CheckSocketError(lpClientContext);
						}
						if (lpClientContext->LastError != WSAECONNRESET && lpClientContext->LastError != 0)
						{
							sprintf_s(Buffer,sizeof(Buffer),"Failed to receive data with WSA error %ld for ID %ld",(long) lpClientContext->LastError,lpClientContext->ConnectionID);
							UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
						}
						else
						{
							sprintf_s(Buffer,sizeof(Buffer),"Failed to receive data because connection reset by client ID %ld",lpClientContext->ConnectionID);
							UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
						}
						CloseClient(lpClientContext,FALSE);
					}
				}
			}
			if ((long) IoSize >= 0 && lpClientContext != NULL)
			{
				// Process data that was accepted
				lpClientContext->BufferPosition += (long) IoSize;
				if (lpClientContext->BufferPosition < 0)
					lpClientContext->BufferPosition = 0;
				else if (lpClientContext->BufferPosition >= sizeof(lpClientContext->Buffer))
					lpClientContext->BufferPosition = sizeof(lpClientContext->Buffer)-1;
				lpClientContext->Buffer[lpClientContext->BufferPosition] = '\0';
				_time64(&lpClientContext->LastAccess);
				#ifdef TESTING_DETAILED_LOGGING
				if (!ServiceTerminating)
				{
					sprintf_s(Buffer,sizeof(Buffer),"Accepted %ld bytes of data",(long) IoSize);
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
				}
				#endif
				#ifdef TESTING_RECV_LOGGING
				if (!ServiceTerminating && lpClientContext->CurrentState != STATE_DATA)
					UpdateLogFile(lpClientContext->AddressString,"Buffer",lpClientContext->Buffer);
				#endif
			}
			else
				continue;
		}
		if (lpClientContext == NULL || lpClientContext->SafeToDelete)
		{
			#ifdef TESTING_DETAILED_LOGGING
			UpdateLogFile((lpClientContext == NULL ? "Unknown" : lpClientContext->AddressString),(lpClientContext == NULL ? "-" : GetConnectionTag(lpClientContext)),"Invalid client context");
			#endif
			if (!SharedThreads || (SharedThreads && ServiceTerminating))
			{
				#ifdef TESTING_PROCESS_LOGGING
				UpdateLogFile((lpClientContext == NULL ? "Unknown" : lpClientContext->AddressString),(lpClientContext == NULL ? "-" : GetConnectionTag(lpClientContext)),"Exiting worker thread");
				#endif
				return(0);
			}
			else
				continue;
		}
		if (lpClientContext->TerminationMessage)
		{
			#ifdef TESTING_DETAILED_LOGGING
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Client context terminated");
			#endif
			if (!SharedThreads || (SharedThreads && ServiceTerminating))
			{
				#ifdef TESTING_PROCESS_LOGGING
				UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Exiting worker thread");
				#endif
				return(0);
			}
			else
				continue;
		}
		if ((lpClientContext->Timeout || lpClientContext->TerminationMessage) && lpClientContext->CurrentState == STATE_DATA && lpClientContext->FileOpen)
		{
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Message is incomplete");
			lpClientContext->MessageIncomplete = TRUE;
			lpClientContext->BufferPosition = 0;
			BufferSize = strlen(lpClientContext->Buffer);
			if (BufferSize < 0)
				BufferSize = 0;
			else if (BufferSize >= sizeof(lpClientContext->Buffer))
				BufferSize = sizeof(lpClientContext->Buffer)-1;
			lpClientContext->Buffer[BufferSize] = '\0';
			if (BufferSize > 0)
			{
				lpClientContext->MessageSize += strlen(lpClientContext->Buffer);
				if (lpClientContext->FileOpen)
					fprintf(lpClientContext->MessageFile,"%s",lpClientContext->Buffer);
			}
			if (lpClientContext->FileOpen)
			{
				fclose(lpClientContext->MessageFile);
				lpClientContext->FileOpen = FALSE;
			}
			lpClientContext->BufferPosition = 0;
			memset(lpClientContext->Buffer,0,sizeof(lpClientContext->Buffer));
			lpClientContext->CurrentState = STATE_PROCESS;
		}
		if ((lpClientContext->Timeout || lpClientContext->TerminationMessage) && (lpClientContext->MessageSize == 0 || lpClientContext->CurrentState < STATE_DATA))
		{
			lpClientContext->CurrentState = STATE_QUIT;
			_time64(&lpClientContext->LastAccess);
			lpClientContext->SafeToDelete = TRUE;
		}
		if (ServiceTerminating || lpClientContext->CurrentState == STATE_QUIT || (!SharedThreads && lpClientContext->ThreadHandle == NULL))
		{
			if (!SharedThreads || (SharedThreads && !lpClientContext->ThreadExited))
			{
				#ifdef TESTING_PROCESS_LOGGING
				if (SharedThreads)
				{
					if (ServiceTerminating)
					{
						sprintf_s(Buffer,sizeof(Buffer),"Shutting down shared worker thread for ID %ld",lpClientContext->ConnectionID);
						UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					}
					else
					{
						sprintf_s(Buffer,sizeof(Buffer),"Exiting shared worker thread for ID %ld",lpClientContext->ConnectionID);
						UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					}
				}
				else
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Shutting down worker thread");
				#endif
				_time64(&lpClientContext->LastAccess);
				lpClientContext->SafeToDelete = TRUE;
				lpClientContext->ThreadExited = TRUE;
			}
			if (!SharedThreads || ServiceTerminating)
				return(0);
			else
				continue;
		}
		if (lpClientContext->BufferPosition > 0 || lpClientContext->Timeout || lpClientContext->TerminationMessage || lpClientContext->CurrentState > STATE_DATA)
		{
			FoundEndOfLine = FALSE;
			CommandStart = lpClientContext->Buffer;
			if (!lpClientContext->Timeout && !lpClientContext->TerminationMessage && lpClientContext->CurrentState != STATE_DATA)
			{
				// Find first non-space
				Pointer = lpClientContext->Buffer;
				while (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && *Pointer != '\0' && (*Pointer == ' ' || *Pointer == '\t'))
					Pointer++;
				CommandStart = Pointer;
				if (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer)-4)
					Command = GetCommand(Pointer);
				else
					Command = COMMAND_UNKNOWN;
				AltPointer = Pointer;
				while (!FoundEndOfLine && AltPointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && *AltPointer != '\0')
				{
					if (*AltPointer == '\n')
						FoundEndOfLine = TRUE;
					else
						AltPointer++;
				}
			}
			if ((lpClientContext->Timeout || lpClientContext->TerminationMessage) && lpClientContext->CurrentState != STATE_DATA)
			{
				// Ignore the command
			}
			else if (lpClientContext->CurrentState != STATE_DATA && !FoundEndOfLine)
			{
				// wait for end of line
			}
			else if (lpClientContext->CurrentState != STATE_DATA && CommandLenError(Command,CommandStart))
			{
				sprintf_s(Buffer,sizeof(Buffer),"501 Syntax error\r\n");
				SendData(lpClientContext,Buffer,strlen(Buffer));
				UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Command length error");
			}
			else if (lpClientContext->CurrentState != STATE_DATA && Command == COMMAND_HELP)
				SendHelp(lpClientContext);
			else if (lpClientContext->CurrentState != STATE_DATA && Command == COMMAND_VRFY)
			{
				Pointer += 4;
				while (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && *Pointer == ' ')
					Pointer++;
				ExtractAddress(Pointer,VRFYBuffer,sizeof(VRFYBuffer),FALSE);
				if (ValidAddress(VRFYBuffer))
					sprintf_s(Buffer,sizeof(Buffer),"252 Cannot VRFY user, but will take message for <%s>\r\n",VRFYBuffer);
				else
				{
					sprintf_s(Buffer,sizeof(Buffer),"553 Malformed address\r\n");
					lpClientContext->ClientErrorCount++;
				}
				SendData(lpClientContext,Buffer,strlen(Buffer));
			}
			else if (lpClientContext->CurrentState != STATE_DATA && Command == COMMAND_NOOP)
			{
				sprintf_s(Buffer,sizeof(Buffer),"250 OK\r\n");
				SendData(lpClientContext,Buffer,strlen(Buffer));
			}
			else if (lpClientContext->CurrentState != STATE_DATA && Command == COMMAND_QUIT)
			{
				lpClientContext->CurrentState = STATE_QUIT;
				sprintf_s(Buffer,sizeof(Buffer),"221 Closing connection\r\n");
				SendData(lpClientContext,Buffer,strlen(Buffer));
				OpenClients = CurrentClients();
				EnterCriticalSection(&LocalCriticalSection);
				if (OpenClients == (!lpClientContext->SafeToDelete ? 1 : 0))
				{
					if (LocalAccessCount != 0)
					{
						UpdateLogFile("Reset","LocalAccessCount","to correct value");
						LocalAccessCount = 0;
					}
					if (DomainAccessCount != 0)
					{
						UpdateLogFile("Reset","DomainAccessCount","to correct value");
						DomainAccessCount = 0;
					}
					if (KeywordAccessCount != 0)
					{
						UpdateLogFile("Reset","KeywordAccessCount","to correct value");
						KeywordAccessCount = 0;
					}
				}
				LeaveCriticalSection(&LocalCriticalSection);
				#ifdef TESTING_DETAILED_LOGGING
				sprintf_s(Buffer,sizeof(Buffer),"QUIT, %d active connections, %d total",OpenClients-(!lpClientContext->SafeToDelete ? 1 : 0),ContextArraySize);
				#else
				sprintf_s(Buffer,sizeof(Buffer),"QUIT");
				#endif
				UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
				CloseClient(lpClientContext,TRUE);
				_time64(&lpClientContext->LastAccess);
				lpClientContext->SafeToDelete = TRUE;
			}
			else if (lpClientContext->CurrentState != STATE_DATA && Command == COMMAND_RSET)
			{
				if (lpClientContext->CurrentState != STATE_HELO)
					lpClientContext->CurrentState = STATE_MAIL;
				if (!lpClientContext->SocketOpen)
				{
					lpClientContext->CurrentState = STATE_QUIT;
					_time64(&lpClientContext->LastAccess);
					lpClientContext->SafeToDelete = TRUE;
				}
				ResetContext(lpClientContext,TRUE);
				sprintf_s(Buffer,sizeof(Buffer),"250 Reset OK\r\n");
				SendData(lpClientContext,Buffer,strlen(Buffer));
				UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"RSET");
			}
			else if (lpClientContext->CurrentState != STATE_DATA && Command == COMMAND_STAT)
			{
				UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"STAT");
				EnterCriticalSection(&CriticalSection);
				sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-Server Status:\r\n");
				_time64(&CurrentTime);
				for (Loop = ContextArraySize-1; Loop >= 0; Loop--)
					if (!ContextArray[Loop]->SafeToDelete)
					{
						sprintf_s(Buffer,sizeof(Buffer),"ID=%ld, Time=%ld, Size=%ld, Error=%ld, State=",(long) ContextArray[Loop]->ConnectionID,(long) (CurrentTime-ContextArray[Loop]->LastAccess),ContextArray[Loop]->MessageSize,(long) ContextArray[Loop]->LastError);
						switch (ContextArray[Loop]->CurrentState)
						{
							case STATE_HELO:	strcat_s(Buffer,sizeof(Buffer),"HELO");
												break;
							case STATE_MAIL:	strcat_s(Buffer,sizeof(Buffer),"MAIL FROM:");
												break;
							case STATE_RCPT:	strcat_s(Buffer,sizeof(Buffer),"RCPT TO:");
												break;
							case STATE_DATA:	strcat_s(Buffer,sizeof(Buffer),"DATA");
												break;
							case STATE_PROCESS:	if (ContextArray[Loop]->ScanStep < 1)
													strcat_s(Buffer,sizeof(Buffer),"Scanning");
												else if (ContextArray[Loop]->ScanStep > 2)
													strcat_s(Buffer,sizeof(Buffer),"Scan 100%");
												else
												{
													sprintf_s(PercentString,sizeof(PercentString),"%ld%%",(ContextArray[Loop]->ScanSize > 0 ? (ContextArray[Loop]->ScanPosition*50)/ContextArray[Loop]->ScanSize : 0)+(ContextArray[Loop]->ScanStep == 2 ? 50 : 0));
													strcat_s(Buffer,sizeof(Buffer),"Scan ");
													strcat_s(Buffer,sizeof(Buffer),PercentString);
												}
												break;
							case STATE_FORWARD:	strcat_s(Buffer,sizeof(Buffer),"Forwarding");
												break;
							case STATE_QUIT:	strcat_s(Buffer,sizeof(Buffer),"Complete");
												break;
							default:			strcat_s(Buffer,sizeof(Buffer),"Unknown");
												break;
						}
						UpdateLogFile(ContextArray[Loop]->AddressString,"-",Buffer);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-[");
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),ContextArray[Loop]->AddressString);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"] - ");
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");

						#ifdef TESTING_EXTENDED_STATUS
						sprintf_s(Buffer,sizeof(Buffer),"Timeout=%d, Incomplete=%d, Truncated=%d, FileOpen=%d",ContextArray[Loop]->Timeout,ContextArray[Loop]->MessageIncomplete,ContextArray[Loop]->MessageTruncated,ContextArray[Loop]->FileOpen);
						UpdateLogFile(ContextArray[Loop]->AddressString,"-",Buffer);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-[");
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),ContextArray[Loop]->AddressString);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"]   ");
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
						sprintf_s(Buffer,sizeof(Buffer),"SocketOpen=%d, Buffer=%ld, WhiteList=%d, BlackList=%d",ContextArray[Loop]->SocketOpen,ContextArray[Loop]->BufferPosition,ContextArray[Loop]->WhiteList,ContextArray[Loop]->BlackListType);
						UpdateLogFile(ContextArray[Loop]->AddressString,"-",Buffer);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-[");
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),ContextArray[Loop]->AddressString);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"]   ");
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
						#endif
					}
				TimeDays = TotalProcessTime/8640000;
				TimeHours = (TotalProcessTime-(TimeDays*8640000))/360000;
				TimeMinutes = (TotalProcessTime-(TimeDays*8640000)-(TimeHours*360000))/6000;
				sprintf_s(Buffer,sizeof(Buffer),"Process Time DHM=%ld:%02d:%02d, Min=%4.2f, Max=%4.2f, Avr=%4.2f",TimeDays,TimeHours,TimeMinutes,((float) MinProcessTime)/100,((float) MaxProcessTime)/100,(TotalMessages > 0 ? (((float) TotalProcessTime)/TotalMessages)/100 : 0.0f));
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
				UpdateLogFile("SpamHater","-",Buffer);
				TimeRunning = CurrentTime-TimeStarted;
				TimeDays = (long) (TimeRunning/86400);
				TimeHours = (long) ((TimeRunning-(TimeDays*86400))/3600);
				TimeMinutes = (long) ((TimeRunning-(TimeDays*86400)-(TimeHours*3600))/60);
				DaysRunning = ((((((float) TimeDays*24)+TimeHours)*60)+TimeMinutes)/60)/24;
				if (DaysRunning > 0)
					DailyCount = (DWORD) (BlackListMessages/DaysRunning);
				else
					DailyCount = 0;
				sprintf_s(Buffer,sizeof(Buffer),"Running DHM=%ld:%02d:%02d, Min Size=%ld, Max Size=%ld, Daily BL=%ld",TimeDays,TimeHours,TimeMinutes,MinProcessSize,MaxProcessSize,DailyCount);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
				UpdateLogFile("SpamHater","-",Buffer);
				sprintf_s(Buffer,sizeof(Buffer),"Total Messages=%ld, Black List=%ld (%4.2f), White List=%ld (%4.2f)",TotalMessages,BlackListMessages,(TotalMessages > 0 ? (((float) BlackListMessages)*100)/TotalMessages : 0.0f),WhiteListMessages,(TotalMessages > 0 ? (((float) WhiteListMessages)*100)/TotalMessages : 0.0f));
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
				UpdateLogFile("SpamHater","-",Buffer);
				sprintf_s(Buffer,sizeof(Buffer),"BL Type: IP=%ld (%4.2f), Conn=%ld, Dom=%ld, HTML=%ld, DNSBL=%ld",BlackListSub[BL_IP][BL_SUB_TOTAL],(BlackListMessages > 0 ? (((float) BlackListSub[BL_IP][BL_SUB_TOTAL])*100)/BlackListMessages : 0.0f),BlackListSub[BL_IP][BL_SUB_IP_CONNECT],BlackListSub[BL_IP][BL_SUB_IP_DOMAIN],BlackListSub[BL_IP][BL_SUB_IP_HTML],BlackListSub[BL_IP][BL_SUB_IP_DNSBL]);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
				UpdateLogFile("SpamHater","-",Buffer);
				sprintf_s(Buffer,sizeof(Buffer),"    Domain =%ld (%4.2f), Address=%ld, Suspect=%ld, Reverse=%ld",BlackListSub[BL_DOMAIN][BL_SUB_TOTAL],(BlackListMessages > 0 ? (((float) BlackListSub[BL_DOMAIN][BL_SUB_TOTAL])*100)/BlackListMessages : 0.0f),BlackListSub[BL_DOMAIN][BL_SUB_DOMAIN_ADDRESS],BlackListSub[BL_DOMAIN][BL_SUB_DOMAIN_SUSPECT],BlackListSub[BL_DOMAIN][BL_SUB_DOMAIN_REVERSE]);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
				UpdateLogFile("SpamHater","-",Buffer);
				sprintf_s(Buffer,sizeof(Buffer),"    Keyword=%ld (%4.2f), Subject=%ld, Body=%ld",BlackListSub[BL_KEYWORD][BL_SUB_TOTAL],(BlackListMessages > 0 ? (((float) BlackListSub[BL_KEYWORD][BL_SUB_TOTAL])*100)/BlackListMessages : 0.0f),BlackListSub[BL_KEYWORD][BL_SUB_KEYWORD_SUBJECT],BlackListSub[BL_KEYWORD][BL_SUB_KEYWORD_BODY]);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
				UpdateLogFile("SpamHater","-",Buffer);
				sprintf_s(Buffer,sizeof(Buffer),"    Format =%ld (%4.2f), Address=%ld, Body=%ld",BlackListSub[BL_FORMAT][BL_SUB_TOTAL],(BlackListMessages > 0 ? (((float) BlackListSub[BL_FORMAT][BL_SUB_TOTAL])*100)/BlackListMessages : 0.0f),BlackListSub[BL_FORMAT][BL_SUB_FORMAT_FROM],BlackListSub[BL_FORMAT][BL_SUB_FORMAT_BODY]);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
				UpdateLogFile("SpamHater","-",Buffer);
				sprintf_s(Buffer,sizeof(Buffer),"    Tag    =%ld (%4.2f), Header=%ld, Admin Command=%ld",BlackListSub[BL_TAG][BL_SUB_TOTAL],(BlackListMessages > 0 ? (((float) BlackListSub[BL_TAG][BL_SUB_TOTAL])*100)/BlackListMessages : 0.0f),BlackListSub[BL_TAG][BL_SUB_TAG_HEADER],BlackListSub[BL_TAG][BL_SUB_TAG_ADMIN]);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
				UpdateLogFile("SpamHater","-",Buffer);
				sprintf_s(Buffer,sizeof(Buffer),"Denied Connections=%ld, Messages Deleted=%ld, Outbreak Messages=%ld",DeniedConnections,MessagesDeleted,OutbreakCount);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
				UpdateLogFile("SpamHater","-",Buffer);
				sprintf_s(Buffer,sizeof(Buffer),"Tracking Log Size=%ld, Outbreak Log Size=%ld, Threads=%d/%d",TrackingLogSize,OutbreakLogSize,ThreadsCreated,ContextArraySize);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
				strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
				UpdateLogFile("SpamHater","-",Buffer);
				LeaveCriticalSection(&CriticalSection);

				#ifdef TESTING_MEMORY_LOGGING
				{
					MEMORY_BLOCK	*CurrentEntry;
					int				FreeBlocks,UsedBlocks,Loop,MaxBlocks,Count;

					EnterCriticalSection(&MemoryCriticalSection);
					CurrentEntry = MemoryBlocks;
					while (CurrentEntry != NULL)
					{
						FreeBlocks = 0;
						UsedBlocks = 0;
						MaxBlocks = 0;
						Count = 0;
						for (Loop = 0; Loop < ALLOC_BLOCKS; Loop++)
						{
							if (CurrentEntry->Allocation[Loop])
							{
								UsedBlocks++;
								Count = 0;
							}
							else
							{
								FreeBlocks++;
								Count++;
								if (Count > MaxBlocks)
									MaxBlocks = Count;
							}
						}
						sprintf_s(Buffer,sizeof(Buffer),"Memory Block:  Temp=%s, Free/Used=%d/%d, First/Max=%d/%d",(CurrentEntry->TemporaryStorage ? "Y" : "N"),FreeBlocks,UsedBlocks,CurrentEntry->FirstFree,MaxBlocks);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214-");
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),Buffer);
						strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n");
						UpdateLogFile("SpamHater","-",Buffer);
						CurrentEntry = (MEMORY_BLOCK *) CurrentEntry->pvNext;
					}
					LeaveCriticalSection(&MemoryCriticalSection);
				}
				#endif

				if (ServiceOnHold)
					strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214 Service on Hold\r\n");
				else
					strcat_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"214 Status OK\r\n");
				SendData(lpClientContext,lpClientContext->Buffer,strlen(lpClientContext->Buffer));
				FlushLogBuffers();
				CheckSocketTimeouts();
			}
			else if (lpClientContext->CurrentState != STATE_DATA && (Command == COMMAND_KILL || Command == COMMAND_WLST || Command == COMMAND_BLST || Command == COMMAND_CTRK || Command == COMMAND_LTRK || Command == COMMAND_STRK || Command == COMMAND_HOLD || Command == COMMAND_CSTA || Command == COMMAND_COBK || Command == COMMAND_LCFG))
			{
				if (Command != COMMAND_CTRK && Command != COMMAND_LTRK && Command != COMMAND_STRK && Command != COMMAND_HOLD && Command != COMMAND_CSTA && Command != COMMAND_COBK && Command != COMMAND_LCFG)
				{
					Pointer += 4;
					while (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && *Pointer == ' ')
						Pointer++;
					if (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer))
						KillConnect = atol(Pointer);
				}
				else
					KillConnect = 0;
				sprintf_s(Buffer,sizeof(Buffer),"451 Request denied\r\n");
				UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),lpClientContext->Buffer);
				if (LocalAddress("",lpClientContext->AddressString))
				{
					sprintf_s(Buffer,sizeof(Buffer),"451 Connection not found\r\n");
					if (Command == COMMAND_CTRK)
					{
						EnterCriticalSection(&TrackingCriticalSection);
						EmptyTrackingLogFile();
						LeaveCriticalSection(&TrackingCriticalSection);
						sprintf_s(Buffer,sizeof(Buffer),"250 Tracking log cleared\r\n");
					}
					else if (Command == COMMAND_COBK)
					{
						// Clearing outbreak list
						EnterCriticalSection(&OutbreakCriticalSection);
						EmptyOutbreakFile();
						LeaveCriticalSection(&OutbreakCriticalSection);
						sprintf_s(Buffer,sizeof(Buffer),"250 Outbreak list cleared\r\n");
					}
					else if (Command == COMMAND_LCFG)
					{
						// Reload configuration from registry
						// Some settings may still not take affect until the service is restarted
						EnterCriticalSection(&CriticalSection);
						ConfigLoaded = LoadConfiguration(FALSE);
						LeaveCriticalSection(&CriticalSection);
						if (ConfigLoaded)
							sprintf_s(Buffer,sizeof(Buffer),"250 Configuration loaded\r\n");
						else
							sprintf_s(Buffer,sizeof(Buffer),"500 Failed to load configuration\r\n");
					}
					else if (Command == COMMAND_LTRK)
					{
						LoadTrackingLogFile(lpClientContext);
						sprintf_s(Buffer,sizeof(Buffer),"250 Tracking log loaded\r\n");
					}
					else if (Command == COMMAND_STRK)
					{
						SaveTrackingLogFile(lpClientContext);
						sprintf_s(Buffer,sizeof(Buffer),"250 Tracking log saved\r\n");
					}
					else if (Command == COMMAND_HOLD)
					{
						if (ServiceOnHold)
						{
							ServiceOnHold = FALSE;
							sprintf_s(Buffer,sizeof(Buffer),"250 Service running.  New connections are being accepted.\r\n");
						}
						else
						{
							ServiceOnHold = TRUE;
							sprintf_s(Buffer,sizeof(Buffer),"250 Service on hold.  New connections are being blocked.\r\n");
						}
					}
					else if (Command == COMMAND_CSTA)
					{
						// Clearing statistics
						EnterCriticalSection(&CriticalSection);
						TotalProcessTime = 0;
						_time64(&TimeStarted);
						MaxProcessTime = 0;
						MinProcessTime = 0;
						MaxProcessSize = 0;
						MinProcessSize = 0;
						TotalMessages = 0;
						BlackListMessages = 0;
						WhiteListMessages = 0;
						DeniedConnections = 0;
						MessagesDeleted = 0;
						OutbreakCount = 0;
						for (Loop = 0; Loop < BL_TOTAL_STATS; Loop++)
							for (Loop2 = 0; Loop2 < BL_TOTAL_SUB_STATS; Loop2++)
								BlackListSub[Loop][Loop2] = 0;
						LeaveCriticalSection(&CriticalSection);
						sprintf_s(Buffer,sizeof(Buffer),"250 Statistics reset\r\n");
					}
					else if (KillConnect > 0 && KillConnect < 10000)
					{
						EnterCriticalSection(&CriticalSection);
						for (Loop = ContextArraySize-1; Loop >= 0; Loop--)
							if (ContextArray[Loop]->ConnectionID == KillConnect)
							{
								if (Command == COMMAND_KILL)
								{
									CloseClient(ContextArray[Loop],TRUE);
									ContextArray[Loop]->Timeout = TRUE;
									sprintf_s(Buffer,sizeof(Buffer),"250 Connection %ld terminated per request\r\n",KillConnect);
								}
								else if (Command == COMMAND_WLST)
								{
									if (!ContextArray[Loop]->PermBlackList)
									{
										if (!ContextArray[Loop]->WhiteList)
										{
											ContextArray[Loop]->WhiteList = TRUE;
											sprintf_s(ContextArray[Loop]->FilteredBy,sizeof(ContextArray[Loop]->FilteredBy),"Admin White List");
											sprintf_s(Buffer,sizeof(Buffer),"250 Connection %ld on White List per Admin\r\n",KillConnect);
										}
										else
											sprintf_s(Buffer,sizeof(Buffer),"250 Connection %ld already on White List\r\n",KillConnect);
									}
									else
										sprintf_s(Buffer,sizeof(Buffer),"451 Connection %ld is on Permanent Black List\r\n",KillConnect);
								}
								else if (Command == COMMAND_BLST)
								{
									if (!ContextArray[Loop]->WhiteList)
									{
										if (ContextArray[Loop]->BlackListType == BL_NONE)
										{
											ContextArray[Loop]->BlackListType = BL_TAG;
											ContextArray[Loop]->BlackListSubType = BL_SUB_TAG_ADMIN;
											ContextArray[Loop]->BlackListResult = FormatErrors;
											sprintf_s(ContextArray[Loop]->FilteredBy,sizeof(ContextArray[Loop]->FilteredBy),"Admin Black List");
											sprintf_s(Buffer,sizeof(Buffer),"250 Connection %ld on Black List per Admin\r\n",KillConnect);
										}
										else
											sprintf_s(Buffer,sizeof(Buffer),"250 Connection %ld already on Black List\r\n",KillConnect);
									}
									else
										sprintf_s(Buffer,sizeof(Buffer),"451 Connection %ld is on White List\r\n",KillConnect);
								}
							}
						LeaveCriticalSection(&CriticalSection);
					}
				}
				SendData(lpClientContext,Buffer,strlen(Buffer));
				UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
			}
			else if (lpClientContext->CurrentState != STATE_DATA && Command == COMMAND_UNKNOWN)
			{
				sprintf_s(Buffer,sizeof(Buffer),"500 Unrecognized command\r\n");
				SendData(lpClientContext,Buffer,strlen(Buffer));
			}
			else if (lpClientContext->ClientErrorCount >= 20)
			{
				// If repeated errors then kill connnection
				UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Connection terminated due to repeated errors");
				lpClientContext->CurrentState = STATE_QUIT;
				_time64(&lpClientContext->LastAccess);
				CloseClient(lpClientContext,TRUE);
				lpClientContext->SafeToDelete = TRUE;
			}
			else if (lpClientContext->CurrentState == STATE_HELO || (lpClientContext->CurrentState != STATE_DATA && (Command == COMMAND_EHLO || Command == COMMAND_HELO)))
			{
				if (lpClientContext->ConnectionID == 0 && (Command == COMMAND_EHLO || Command == COMMAND_HELO))
				{
					EnterCriticalSection(&CriticalSection);
					lpClientContext->ConnectionID = NextConnectionID;
					NextConnectionID++;
					if (NextConnectionID >= 10000)
						NextConnectionID = 1;
					LeaveCriticalSection(&CriticalSection);
				}
				switch (Command)
				{
					case COMMAND_EHLO:
					case COMMAND_HELO:		// Find next non-space
											_time64(&lpClientContext->LastAccess);
											Pointer += 4;
											while (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && *Pointer == ' ')
												Pointer++;
											if (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer))
											{
												strcpy_s(lpClientContext->HELOcmd,sizeof(lpClientContext->HELOcmd),lpClientContext->Buffer);
												lpClientContext->HELOAddress = lpClientContext->HELOcmd+(Pointer-lpClientContext->Buffer);
												if (Command == COMMAND_EHLO)
												{
													if (*lpClientContext->HELOAddress != '\r' && *lpClientContext->HELOAddress != '\n' && *lpClientContext->HELOAddress != '\0')
														sprintf_s(Buffer,sizeof(Buffer),"250-Hello [%s] %s250-SIZE %ld\r\n",lpClientContext->AddressString,lpClientContext->HELOAddress,MaxMessageSize);
													else
														sprintf_s(Buffer,sizeof(Buffer),"250-Hello [%s]\r\n250-SIZE %ld\r\n",lpClientContext->AddressString,MaxMessageSize);
													strcat_s(Buffer,sizeof(Buffer),"250-HELP\r\n");
													strcat_s(Buffer,sizeof(Buffer),"250-VRFY\r\n");
													strcat_s(Buffer,sizeof(Buffer),"250-DSN\r\n");
													strcat_s(Buffer,sizeof(Buffer),"250 OK\r\n");
													SendData(lpClientContext,Buffer,strlen(Buffer));
												}
												else
												{
													if (*lpClientContext->HELOAddress != '\r' && *lpClientContext->HELOAddress != '\n' && *lpClientContext->HELOAddress != '\0')
														sprintf_s(Buffer,sizeof(Buffer),"250 Hello %s",lpClientContext->HELOAddress);
													else
														sprintf_s(Buffer,sizeof(Buffer),"250-Hello [%s]\r\n",lpClientContext->AddressString);
													SendData(lpClientContext,Buffer,strlen(Buffer));
												}
												UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),lpClientContext->HELOcmd);
												if (lpClientContext->CurrentState == STATE_HELO)
													lpClientContext->CurrentState = STATE_MAIL;
											}
											if (!lpClientContext->SocketOpen)
											{
												lpClientContext->CurrentState = STATE_QUIT;
												_time64(&lpClientContext->LastAccess);
												lpClientContext->SafeToDelete = TRUE;
											}
											break;
					default:				sprintf_s(Buffer,sizeof(Buffer),"503 Bad command sequence\r\n");
											SendData(lpClientContext,Buffer,strlen(Buffer));
											break;
				}
			}
			else if (lpClientContext->CurrentState == STATE_MAIL)
			{
				if (lpClientContext->ConnectionID == 0 && Command == COMMAND_MAIL)
				{
					// Check if IP has been put on the Deny Connection list and close it, if necessary
					if (DomainFilters != NULL && ConvertIPString(lpClientContext->AddressString,&Num1,&Num2,&Num3,&Num4))
					{
						EnterCriticalSection(&DomainCriticalSection);
						DomainAccessCount++;
						LeaveCriticalSection(&DomainCriticalSection);
						FilterList = DomainFilters;
						while (lpClientContext->CurrentState != STATE_QUIT && FilterList != NULL)
						{
							// Check only black listed IP addresses
							if ((FilterList->Filter[0] == '1' || FilterList->Filter[0] == '2') && FilterList->Filter[1] == '0' && FilterList->Filter[2] == '3')
								if (IPInSubnet((unsigned char) FilterList->Filter[4],(unsigned char) FilterList->Filter[5],(unsigned char) FilterList->Filter[6],(unsigned char) FilterList->Filter[7],(unsigned char) FilterList->Filter[8],(unsigned char) FilterList->Filter[9],(unsigned char) FilterList->Filter[10],(unsigned char) FilterList->Filter[11],Num1,Num2,Num3,Num4))
								{
									EnterCriticalSection(&CriticalSection);
									DeniedConnections++;
									LeaveCriticalSection(&CriticalSection);
									UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Connection denied");
									lpClientContext->CurrentState = STATE_QUIT;
									_time64(&lpClientContext->LastAccess);
									CloseClient(lpClientContext,TRUE);
									lpClientContext->SafeToDelete = TRUE;
								}
							FilterList = (FILTER_ENTRY *) FilterList->pvNext;
						}
						EnterCriticalSection(&DomainCriticalSection);
						DomainAccessCount--;
						LeaveCriticalSection(&DomainCriticalSection);
					}
					if (lpClientContext->CurrentState != STATE_QUIT)
					{
						EnterCriticalSection(&CriticalSection);
						lpClientContext->ConnectionID = NextConnectionID;
						NextConnectionID++;
						if (NextConnectionID >= 10000)
							NextConnectionID = 1;
						LeaveCriticalSection(&CriticalSection);
					}
				}
				switch (Command)
				{
					case COMMAND_MAIL:		// Find next non-space
											Pointer += 5;
											while (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && *Pointer == ' ')
												Pointer++;
											if (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer)-4)
												SecondCommand = GetCommand(Pointer);
											else
												SecondCommand = COMMAND_UNKNOWN;
											if (SecondCommand == COMMAND_FROM)
											{
												// Find next non-space
												_time64(&lpClientContext->LastAccess);
												Pointer += 5;
												while (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && *Pointer == ' ')
													Pointer++;
												if (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && strlen(Pointer) > 0)
												{
													strcpy_s(lpClientContext->MAILcmd,sizeof(lpClientContext->MAILcmd),lpClientContext->Buffer);
													ExtractAddress(lpClientContext->MAILcmd+(Pointer-lpClientContext->Buffer),lpClientContext->MAILAddress,sizeof(lpClientContext->MAILAddress),TRUE);
													if (ValidAddress(lpClientContext->MAILAddress) || (AcceptBlankMailFrom && strlen(lpClientContext->MAILAddress) == 0))
													{
														// Analyse message size indicator, if any
														SizeParam = 0;
														AltPointer = &lpClientContext->MAILcmd[strlen(lpClientContext->MAILcmd)-1];
														while (AltPointer > &lpClientContext->MAILcmd[4] && (isdigit(AltPointer[0]) || AltPointer[0] == '\r' || AltPointer[0] == '\n'))
															AltPointer--;
														if (AltPointer[0] == '=')
														{
															AltPointer -= 4;
															if (toupper(AltPointer[0]) == 'S' && toupper(AltPointer[1]) == 'I' && toupper(AltPointer[2]) == 'Z' && toupper(AltPointer[3]) == 'E')
															{
																AltPointer += 5;
																SizeParam = atol(AltPointer);
															}
														}
														if (SizeParam > 0 && MaxMessageSize > 0 && SizeParam > MaxMessageSize)
														{
															sprintf_s(Buffer,sizeof(Buffer),"552 Maximum message size exceeded\r\n");
															SendData(lpClientContext,Buffer,strlen(Buffer));
															UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Maximum message size exceeded");
														}
														else
														{
															if (strlen(lpClientContext->MAILAddress) > 0)
																sprintf_s(Buffer,sizeof(Buffer),"250 Sender %s\r\n",lpClientContext->MAILAddress);
															else
																sprintf_s(Buffer,sizeof(Buffer),"250 Sender [%s]\r\n",lpClientContext->AddressString);
															SendData(lpClientContext,Buffer,strlen(Buffer));
															UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),lpClientContext->MAILcmd);
															lpClientContext->CurrentState = STATE_RCPT;
														}
														if (!lpClientContext->SocketOpen)
														{
															lpClientContext->CurrentState = STATE_QUIT;
															_time64(&lpClientContext->LastAccess);
															lpClientContext->SafeToDelete = TRUE;
														}
													}
													else
													{
														sprintf_s(Buffer,sizeof(Buffer),"553 Malformed address\r\n");
														SendData(lpClientContext,Buffer,strlen(Buffer));
														UpdateLogFile(lpClientContext->AddressString,Buffer,Pointer);
														lpClientContext->ClientErrorCount++;
													}
												}
												else
												{
													sprintf_s(Buffer,sizeof(Buffer),"501 Unrecognized parameter\r\n");
													SendData(lpClientContext,Buffer,strlen(Buffer));
												}
											}
											else
											{
												sprintf_s(Buffer,sizeof(Buffer),"501 Unrecognized parameter\r\n");
												SendData(lpClientContext,Buffer,strlen(Buffer));
											}
											break;
					default:				sprintf_s(Buffer,sizeof(Buffer),"503 Bad command sequence\r\n");
											SendData(lpClientContext,Buffer,strlen(Buffer));
											break;
				}
			}
			else if (lpClientContext->CurrentState == STATE_RCPT)
			{
				if (lpClientContext->ConnectionID == 0 && Command == COMMAND_RCPT)
				{
					EnterCriticalSection(&CriticalSection);
					lpClientContext->ConnectionID = NextConnectionID;
					NextConnectionID++;
					if (NextConnectionID >= 10000)
						NextConnectionID = 1;
					LeaveCriticalSection(&CriticalSection);
				}
				switch (Command)
				{
					case COMMAND_MAIL:		sprintf_s(Buffer,sizeof(Buffer),"503 Sender already specified\r\n");
											SendData(lpClientContext,Buffer,strlen(Buffer));
											break;
					case COMMAND_RCPT:		// Find next non-space
											Pointer += 5;
											while (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && *Pointer == ' ')
												Pointer++;
											if (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer)-4)
												SecondCommand = GetCommand(Pointer);
											else
												SecondCommand = COMMAND_UNKNOWN;
											if (SecondCommand == COMMAND_TO)
											{
												// Find next non-space
												_time64(&lpClientContext->LastAccess);
												Pointer += 3;
												while (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && *Pointer == ' ')
													Pointer++;
												if (Pointer < lpClientContext->Buffer+sizeof(lpClientContext->Buffer) && strlen(Pointer) > 0)
												{
													if (lpClientContext->RCPTCount < COMMAND_MAX_RCPT)
													{
														lpClientContext->RCPTcmdSize[lpClientContext->RCPTCount] = strlen(lpClientContext->Buffer)+1;
														#ifndef MEMORY_NEW_ALLOC
														lpClientContext->RCPTcmd[lpClientContext->RCPTCount] = new char[strlen(lpClientContext->Buffer)+1];
														#else
														lpClientContext->RCPTcmd[lpClientContext->RCPTCount] = (char *) AllocateBlock(lpClientContext->RCPTcmdSize[lpClientContext->RCPTCount],TRUE);
														#endif
														if (lpClientContext->RCPTcmd[lpClientContext->RCPTCount] != NULL)
														{
															strcpy_s(lpClientContext->RCPTcmd[lpClientContext->RCPTCount],strlen(lpClientContext->Buffer)+1,lpClientContext->Buffer);
															lpClientContext->RCPTAddress[lpClientContext->RCPTCount] = lpClientContext->RCPTcmd[lpClientContext->RCPTCount]+(Pointer-lpClientContext->Buffer);
															ExtractAddress(lpClientContext->RCPTAddress[lpClientContext->RCPTCount],Buffer,sizeof(Buffer),FALSE);
															if (ValidAddress(Buffer))
															{
																if (LocalAddress(Buffer,lpClientContext->AddressString))
																{
																	if (RejectIfSameFromAndTo && !lpClientContext->WhiteList && !lpClientContext->PermBlackList && strlen(lpClientContext->MAILAddress) > 0 && _stricmp(lpClientContext->MAILAddress,Buffer) == 0)
																	{
																		lpClientContext->BlackListType = BL_FORMAT;
																		lpClientContext->BlackListSubType = BL_SUB_FORMAT_FROM;
																		sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"Same MAIL FROM: and RCTP TO: %s",lpClientContext->MAILAddress);
																		lpClientContext->BlackListResult = FormatErrors;
																	}
																	lpClientContext->RCPTCount++;
																	sprintf_s(Buffer,sizeof(Buffer),"250 Recipient %s",lpClientContext->RCPTAddress[lpClientContext->RCPTCount-1]);
																	SendData(lpClientContext,Buffer,strlen(Buffer));
																	UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),lpClientContext->RCPTcmd[lpClientContext->RCPTCount-1]);
																}
																else
																{
																	if (lpClientContext->RCPTcmd[lpClientContext->RCPTCount] != NULL)
																	{
																		#ifndef MEMORY_NEW_ALLOC
																		delete [] lpClientContext->RCPTcmd[lpClientContext->RCPTCount];
																		#else
																		ReleaseBlock((void *) lpClientContext->RCPTcmd[lpClientContext->RCPTCount],lpClientContext->RCPTcmdSize[lpClientContext->RCPTCount]);
																		#endif
																		lpClientContext->RCPTcmd[lpClientContext->RCPTCount] = NULL;
																		lpClientContext->RCPTcmdSize[lpClientContext->RCPTCount] = 0;
																	}
																	sprintf_s(Buffer,sizeof(Buffer),"550 Unable to relay for %s",Pointer);
																	SendData(lpClientContext,Buffer,strlen(Buffer));
																	UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
																}
															}
															else
															{
																if (lpClientContext->RCPTcmd[lpClientContext->RCPTCount] != NULL)
																{
																	#ifndef MEMORY_NEW_ALLOC
																	delete [] lpClientContext->RCPTcmd[lpClientContext->RCPTCount];
																	#else
																	ReleaseBlock((void *) lpClientContext->RCPTcmd[lpClientContext->RCPTCount],lpClientContext->RCPTcmdSize[lpClientContext->RCPTCount]);
																	#endif
																	lpClientContext->RCPTcmd[lpClientContext->RCPTCount] = NULL;
																	lpClientContext->RCPTcmdSize[lpClientContext->RCPTCount] = 0;
																}
																sprintf_s(Buffer,sizeof(Buffer),"553 Malformed address\r\n");
																SendData(lpClientContext,Buffer,strlen(Buffer));
																UpdateLogFile(lpClientContext->AddressString,Buffer,Pointer);
																lpClientContext->ClientErrorCount++;
															}
														}
														else
														{
															lpClientContext->RCPTcmdSize[lpClientContext->RCPTCount] = 0;
															sprintf_s(Buffer,sizeof(Buffer),"452 Local error in processing\r\n");
															SendData(lpClientContext,Buffer,strlen(Buffer));
															UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Failed to allocate memory for RCTP list");
														}
													}
													else
													{
														sprintf_s(Buffer,sizeof(Buffer),"450 Maximum RCTP addresses reached\r\n");
														SendData(lpClientContext,Buffer,strlen(Buffer));
														UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Maximum RCTP addresses reached");
													}
												}
												else
												{
													sprintf_s(Buffer,sizeof(Buffer),"501 Unrecognized parameter\r\n");
													SendData(lpClientContext,Buffer,strlen(Buffer));
												}
											}
											else
											{
												sprintf_s(Buffer,sizeof(Buffer),"501 Unrecognized parameter\r\n");
												SendData(lpClientContext,Buffer,strlen(Buffer));
											}
											break;
					case COMMAND_DATA:		if (lpClientContext->RCPTCount > 0)
											{
												_time64(&lpClientContext->LastAccess);
												if (!lpClientContext->FileOpen)
												{
													_time64(&CurrentTime);
													_ctime64_s(Buffer,sizeof(Buffer),&CurrentTime);
													while (strlen(Buffer) > 0 && (Buffer[strlen(Buffer)-1] == '\r' || Buffer[strlen(Buffer)-1] == '\n'))
														Buffer[strlen(Buffer)-1] = '\0';
													Buffer[7] = '\0';
													Buffer[10] = '\0';
													Buffer[13] = '\0';
													Buffer[16] = '\0';
													Buffer[19] = '\0';
													sprintf_s(lpClientContext->FileName,sizeof(lpClientContext->FileName),"%s%s%s-%s%s%s-%04d",&Buffer[20],&Buffer[4],&Buffer[8],&Buffer[11],&Buffer[14],&Buffer[17],lpClientContext->ConnectionID);
													sprintf_s(lpClientContext->FullFileName,sizeof(lpClientContext->FullFileName),"%s%s",TempFilePath,lpClientContext->FileName);
													sprintf_s(lpClientContext->TurfFileName,sizeof(lpClientContext->TurfFileName),"%s%s",TurfDir,lpClientContext->FileName);
													if (_access(lpClientContext->FullFileName,0) == 0)
														remove(lpClientContext->FullFileName);
													lpClientContext->MessageSize = 0;
													memset(lpClientContext->LastChars,0,sizeof(lpClientContext->LastChars));
													if (fopen_s(&lpClientContext->MessageFile,lpClientContext->FullFileName,"wb") == 0)
													{
														lpClientContext->FileOpen = TRUE;
														sprintf_s(Buffer,sizeof(Buffer),"Received: from %s",lpClientContext->HELOAddress);
														while (strlen(Buffer) > 0 && (Buffer[strlen(Buffer)-1] == '\r' || Buffer[strlen(Buffer)-1] == '\n'))
															Buffer[strlen(Buffer)-1] = '\0';
														strcat_s(Buffer,sizeof(Buffer)," ([");
														strcat_s(Buffer,sizeof(Buffer),lpClientContext->AddressString);
														strcat_s(Buffer,sizeof(Buffer),"]) by SpamHater; ");
														BuildDateString(&Buffer[strlen(Buffer)],sizeof(Buffer)-strlen(Buffer)-1);
														strcat_s(Buffer,sizeof(Buffer),"\r\n");
														if (lpClientContext->FileOpen)
															if (fprintf(lpClientContext->MessageFile,"%s",Buffer) < 0)
																lpClientContext->FileOpen = FALSE;

														sprintf_s(Buffer,sizeof(Buffer),"354 Start mail input, end with <CRLF>.<CRLF>\r\n");
														SendData(lpClientContext,Buffer,strlen(Buffer));
														UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"DATA");
														lpClientContext->CurrentState = STATE_DATA;
														if (!lpClientContext->SocketOpen)
														{
															lpClientContext->CurrentState = STATE_QUIT;
															_time64(&lpClientContext->LastAccess);
															lpClientContext->SafeToDelete = TRUE;
														}
													}
													else
													{
														sprintf_s(Buffer,sizeof(Buffer),"451 Local error in processing\r\n");
														SendData(lpClientContext,Buffer,strlen(Buffer));
														sprintf_s(Buffer,sizeof(Buffer),"Failed to open file %s",lpClientContext->FullFileName);
														UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
													}
												}
												else
												{
													sprintf_s(Buffer,sizeof(Buffer),"451 Local error in processing\r\n");
													SendData(lpClientContext,Buffer,strlen(Buffer));
													sprintf_s(Buffer,sizeof(Buffer),"File %s already open",lpClientContext->FullFileName);
													UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
												}
											}
											else
											{
												sprintf_s(Buffer,sizeof(Buffer),"503 Bad command sequence\r\n");
												SendData(lpClientContext,Buffer,strlen(Buffer));
											}
											break;
					default:				sprintf_s(Buffer,sizeof(Buffer),"503 Bad command sequence\r\n");
											SendData(lpClientContext,Buffer,strlen(Buffer));
											break;
				}
			}
			else if (lpClientContext->CurrentState == STATE_DATA && !lpClientContext->TerminationMessage)
			{
				if (strlen(lpClientContext->Buffer) >= 5)
					strcpy_s(lpClientContext->LastChars,sizeof(lpClientContext->LastChars),&lpClientContext->Buffer[strlen(lpClientContext->Buffer)-5]);
				else
				{
					for (Loop = 0; Loop < (int) strlen(lpClientContext->Buffer); Loop++)
					{
						lpClientContext->LastChars[0] = lpClientContext->LastChars[1];
						lpClientContext->LastChars[1] = lpClientContext->LastChars[2];
						lpClientContext->LastChars[2] = lpClientContext->LastChars[3];
						lpClientContext->LastChars[3] = lpClientContext->LastChars[4];
						lpClientContext->LastChars[4] = lpClientContext->Buffer[Loop];
						lpClientContext->LastChars[5] = '\0';
					}
				}
				if (lpClientContext->FileOpen && strlen(lpClientContext->Buffer) > 0 && strlen(lpClientContext->Buffer) < sizeof(lpClientContext->Buffer))
				{
					lpClientContext->MessageSize += strlen(lpClientContext->Buffer);
					if (lpClientContext->FileOpen)
						if (fprintf(lpClientContext->MessageFile,"%s",lpClientContext->Buffer) < 0)
							lpClientContext->FileOpen = FALSE;
					lpClientContext->BufferPosition = 0;
					memset(lpClientContext->Buffer,0,sizeof(lpClientContext->Buffer));
				}
				if (strlen(lpClientContext->Buffer) >= 9 && FindString(lpClientContext->Buffer,"\r\n.\r\nQUIT",SEARCH_CONTAINS))
				{
					strcpy_s(lpClientContext->LastChars,sizeof(lpClientContext->LastChars),"\r\n.\r\n");
					QuitOnEndData = TRUE;
				}
				if ((lpClientContext->Timeout || lpClientContext->TerminationMessage) || (strlen(lpClientContext->LastChars) == 5 && _stricmp(lpClientContext->LastChars,"\r\n.\r\n") == 0))
				{
					if (lpClientContext->FileOpen)
						fclose(lpClientContext->MessageFile);
					lpClientContext->FileOpen = FALSE;
					if (lpClientContext->Timeout || lpClientContext->TerminationMessage)
						sprintf_s(Buffer,sizeof(Buffer),"221 Transmission timeout\r\n");
					else
						sprintf_s(Buffer,sizeof(Buffer),"250 Message queued\r\n");
					if (lpClientContext->SocketOpen)
						SendData(lpClientContext,Buffer,strlen(Buffer));
					lpClientContext->CurrentState = STATE_PROCESS;
				}
				else if (MaxMessageSize > 0 && lpClientContext->MessageSize > MaxMessageSize)
				{
					lpClientContext->MessageTruncated = TRUE;
					if (lpClientContext->FileOpen)
						fclose(lpClientContext->MessageFile);
					lpClientContext->FileOpen = FALSE;
					sprintf_s(Buffer,sizeof(Buffer),"552 Maximum message size exceeded\r\n");
					SendData(lpClientContext,Buffer,strlen(Buffer));
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Maximum message size exceeded");
					lpClientContext->CurrentState = STATE_PROCESS;
				}
			}
			if (lpClientContext->CurrentState == STATE_PROCESS && !lpClientContext->TerminationMessage)
			{
				_ftime64_s(&lpClientContext->StartTime);
				lpClientContext->TimeSpan = 0;
				if (lpClientContext->MessageSize > 0)
				{
					if (!ProcessFilter(lpClientContext))
					{
						UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"ProcessFilter() failed, forwarding message");
						lpClientContext->WhiteList = TRUE;
						lpClientContext->PermBlackList = FALSE;
						sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"ProcessFilter() failure");
					}
					if (AlternateRouting > 0 && lpClientContext->MessageIdentified && ((lpClientContext->WhiteList || lpClientContext->BlackListType == BL_NONE) && !lpClientContext->PermBlackList))
					{
						if (ConnectToDatabase(lpClientContext))
						{
							sprintf_s(Buffer,sizeof(Buffer),"SELECT Initials, EMailAddress FROM Users WHERE Initials='MR'");
							if (ConnectStatement(lpClientContext,Buffer))
							{
								ReturnCode = SQLBindCol(lpClientContext->hAppStmt,1,SQL_C_CHAR,(SQLPOINTER) lpClientContext->DBStrField1,sizeof(lpClientContext->DBStrField1),&lpClientContext->DBStrField1Size);
								ReturnCode = SQLBindCol(lpClientContext->hAppStmt,2,SQL_C_CHAR,(SQLPOINTER) lpClientContext->DBStrField2,sizeof(lpClientContext->DBStrField2),&lpClientContext->DBStrField2Size);
								if ((ReturnCode = SQLFetchScroll(lpClientContext->hAppStmt,SQL_FETCH_NEXT,1)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
									UpdateLogFile("ODBC","Error","Could not retrieve record");
								else
								{
								}
								DisconnectStatement(lpClientContext);
							}
							DisconnectFromDatabase(lpClientContext);
						}
					}
					lpClientContext->CurrentState = STATE_FORWARD;
				}
				else if (!lpClientContext->SocketOpen || QuitOnEndData)
				{
					lpClientContext->CurrentState = STATE_QUIT;
					_time64(&lpClientContext->LastAccess);
					lpClientContext->SafeToDelete = TRUE;
				}
				else
				{
					ResetContext(lpClientContext,TRUE);
					lpClientContext->CurrentState = STATE_MAIL;
				}
			}
			if (lpClientContext->CurrentState == STATE_FORWARD && !lpClientContext->TerminationMessage)
			{
				// If no forwarding address is specified then send it to the TurfDir
				if (lpClientContext->PermBlackList)
					lpClientContext->WhiteList = FALSE;
				if (lpClientContext->BlackListResult == BL_RESULT_FORWARD && strlen(ForwardingAddress) <= 0)
					lpClientContext->BlackListResult = BL_RESULT_TURFDIR;
				EnterCriticalSection(&CriticalSection);
				TotalMessages++;
				_ftime64_s(&lpClientContext->EndTime);
				lpClientContext->TimeSpan = (DWORD) (lpClientContext->EndTime.time-lpClientContext->StartTime.time);
				lpClientContext->TimeSpan *= 100;
				lpClientContext->TimeSpan += (DWORD) (lpClientContext->EndTime.millitm-lpClientContext->StartTime.millitm)/10;
				if (lpClientContext->TimeSpan <= 0 || lpClientContext->TimeSpan > 10000000)
					lpClientContext->TimeSpan = 1;
				TotalProcessTime += lpClientContext->TimeSpan;
				if (MaxProcessTime == 0 || MaxProcessTime < lpClientContext->TimeSpan)
				{
					MaxProcessTime = lpClientContext->TimeSpan;
					MaxProcessSize = lpClientContext->MessageSize;
				}
				if (MinProcessTime == 0 || MinProcessTime >= lpClientContext->TimeSpan)
				{
					MinProcessTime = lpClientContext->TimeSpan;
					if (MinProcessSize == 0 || MinProcessSize > (DWORD) lpClientContext->MessageSize)
						MinProcessSize = lpClientContext->MessageSize;
				}
				LeaveCriticalSection(&CriticalSection);
				if (!lpClientContext->WhiteList && (lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListSubType == BL_SUB_IP_HTML || lpClientContext->BlackListSubType == BL_SUB_KEYWORD_BODY || lpClientContext->BlackListSubType == BL_SUB_IP_DNSBL || lpClientContext->BlackListSubType == BL_SUB_FORMAT_BODY || (lpClientContext->PermBlackList && lpClientContext->BlackListType != BL_IP)))
				{
					RecordIPTracking(lpClientContext);
//					RecordDomainTracking(lpClientContext);
				}
				if (lpClientContext->WhiteRecipient >= 0)
					UpdateLogFile(lpClientContext->AddressString,"Recipient is on","White List");
				if (lpClientContext->WhiteList)
				{
					EnterCriticalSection(&CriticalSection);
					WhiteListMessages++;
					LeaveCriticalSection(&CriticalSection);
					UpdateLogFile(lpClientContext->AddressString,"White List",lpClientContext->FilteredBy);
				}
				else if (lpClientContext->BlackListType != BL_NONE)
				{
					EnterCriticalSection(&CriticalSection);
					BlackListMessages++;
					if (lpClientContext->BlackListResult == BL_RESULT_DELETE)
						MessagesDeleted++;
					BlackListSub[lpClientContext->BlackListType][BL_SUB_TOTAL]++;
					BlackListSub[lpClientContext->BlackListType][lpClientContext->BlackListSubType]++;
					LeaveCriticalSection(&CriticalSection);
					UpdateLogFile(lpClientContext->AddressString,"Black List",lpClientContext->FilteredBy);
//					sprintf_s(Buffer,sizeof(Buffer),"BlackListType=%ld, BlackListSubType=%ld",lpClientContext->BlackListType,lpClientContext->BlackListSubType);
//					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					switch (lpClientContext->BlackListResult)
					{
						case BL_RESULT_TURFDIR:	if (strlen(lpClientContext->TurfFileName) > 0)
													sprintf_s(Buffer,sizeof(Buffer),"Sending to TurfDir as %s",lpClientContext->TurfFileName);
												else
													sprintf_s(Buffer,sizeof(Buffer),"Sending to TurfDir");
												UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
												break;
						case BL_RESULT_FORWARD:	UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Forwarding to Spam address");
												break;
						case BL_RESULT_DELETE:	UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Message deleted");
												break;
						default:				UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Unknown message destination");
												break;
					}
				}
				else
				{
					#ifdef TESTING_DETAILED_LOGGING
					sprintf_s(Buffer,sizeof(Buffer),"unclassified message, MessageSize=%ld (%ld), StepsTaken='%s', %d Links found, %d Links resolved, %d Encoded chars, WhiteList=%ld, PermBlackList=%ld, BlackListType=%ld, BlackListResult=%ld",lpClientContext->MessageSize,(lpClientContext->MessageBody == NULL ? 0 : strlen(lpClientContext->MessageBody)),lpClientContext->StepsTaken,lpClientContext->HTMLLinks,lpClientContext->HTMLLinksResolved,lpClientContext->CharReplacements,lpClientContext->WhiteList,lpClientContext->PermBlackList,lpClientContext->BlackListType,lpClientContext->BlackListResult);
					#else
					sprintf_s(Buffer,sizeof(Buffer),"unclassified message, Steps: '%s', %d Links found, %d Links resolved, %d Encoded chars",lpClientContext->StepsTaken,lpClientContext->HTMLLinks,lpClientContext->HTMLLinksResolved,lpClientContext->CharReplacements);
					#endif
					UpdateLogFile(lpClientContext->AddressString,"Forwarding",Buffer);
				}
				if (!lpClientContext->WhiteList && lpClientContext->BlackListType != BL_NONE && lpClientContext->BlackListResult == BL_RESULT_TURFDIR)
				{
					lpClientContext->ForwardComplete = SendToTurfDir(lpClientContext,lpClientContext->BlackListType);
					if (lpClientContext->WhiteRecipient >= 0)
						ForwardToSmartHost(lpClientContext,FALSE,TRUE);
				}
				else if (!lpClientContext->WhiteList && lpClientContext->BlackListType != BL_NONE && lpClientContext->BlackListResult == BL_RESULT_DELETE)
				{
					lpClientContext->ForwardComplete = TRUE;	// Do nothing with message
					if (lpClientContext->WhiteRecipient >= 0)
						ForwardToSmartHost(lpClientContext,FALSE,TRUE);
				}
				else if (lpClientContext->WhiteList || lpClientContext->BlackListType == BL_NONE || (lpClientContext->BlackListType != BL_NONE && lpClientContext->BlackListResult == BL_RESULT_FORWARD))
				{
					if (!lpClientContext->WhiteList && lpClientContext->BlackListType != BL_NONE && lpClientContext->BlackListResult == BL_RESULT_FORWARD)
					{
						if (lpClientContext->WhiteRecipient >= 0)
							ForwardToSmartHost(lpClientContext,FALSE,TRUE);
						lpClientContext->ForwardComplete = ForwardToSmartHost(lpClientContext,TRUE,FALSE);
					}
					else
						lpClientContext->ForwardComplete = ForwardToSmartHost(lpClientContext,FALSE,FALSE);
				}
				else if (lpClientContext->WhiteRecipient >= 0)
					ForwardToSmartHost(lpClientContext,FALSE,TRUE);
				#ifdef TESTING_KEEP_UNKNOWNS
				if (!lpClientContext->WhiteList && lpClientContext->BlackListType == BL_NONE)
					SendToTurfDir(lpClientContext,lpClientContext->BlackListType);
				#endif
				ResetContext(lpClientContext,TRUE);
				lpClientContext->CurrentState = STATE_MAIL;
				if (!lpClientContext->SocketOpen || QuitOnEndData)
				{
					lpClientContext->CurrentState = STATE_QUIT;
					_time64(&lpClientContext->LastAccess);
					lpClientContext->SafeToDelete = TRUE;
				}
			}
			if (lpClientContext->CurrentState == STATE_QUIT && lpClientContext->SocketOpen && !lpClientContext->TerminationMessage)
			{
				if (QuitOnEndData)
				{
					OpenClients = CurrentClients();
					EnterCriticalSection(&LocalCriticalSection);
					if (OpenClients == (!lpClientContext->SafeToDelete ? 1 : 0))
					{
						if (LocalAccessCount != 0)
						{
							UpdateLogFile("Reset","LocalAccessCount","to correct value");
							LocalAccessCount = 0;
						}
						if (DomainAccessCount != 0)
						{
							UpdateLogFile("Reset","DomainAccessCount","to correct value");
							DomainAccessCount = 0;
						}
						if (KeywordAccessCount != 0)
						{
							UpdateLogFile("Reset","KeywordAccessCount","to correct value");
							KeywordAccessCount = 0;
						}
					}
					LeaveCriticalSection(&LocalCriticalSection);
					#ifdef TESTING_DETAILED_LOGGING
					sprintf_s(Buffer,sizeof(Buffer),"QUIT, %d active connections, %d total",OpenClients-(!lpClientContext->SafeToDelete ? 1 : 0),ContextArraySize);
					#else
					sprintf_s(Buffer,sizeof(Buffer),"QUIT");
					#endif
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
				}
				else
				{
					sprintf_s(Buffer,sizeof(Buffer),"421 Service not available\r\n");
					SendData(lpClientContext,Buffer,strlen(Buffer));
				}
				CloseClient(lpClientContext,TRUE);
			}
			if (!lpClientContext->TerminationMessage)
			{
				if (!lpClientContext->SocketOpen && lpClientContext->CurrentState != STATE_DATA && lpClientContext->CurrentState != STATE_PROCESS && lpClientContext->CurrentState != STATE_FORWARD)
				{
					lpClientContext->CurrentState = STATE_QUIT;
					_time64(&lpClientContext->LastAccess);
					lpClientContext->SafeToDelete = TRUE;
				}
				else if (lpClientContext->CurrentState == STATE_DATA || FoundEndOfLine)
				{
					// Prepare for next line
					lpClientContext->BufferPosition = 0;
					memset(lpClientContext->Buffer,0,sizeof(lpClientContext->Buffer));
				}

				if (SharedThreads && lpClientContext->SocketOpen && lpClientContext->CurrentState != STATE_QUIT && !lpClientContext->ThreadExited)
				{
					// Pend another read request to get the next client request
					#ifdef TESTING_DETAILED_LOGGING
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Pending another read request");
					#endif
					Result = ReadFile((HANDLE) lpClientContext->Socket,&lpClientContext->Buffer[lpClientContext->BufferPosition],(DWORD) sizeof(lpClientContext->Buffer)-lpClientContext->BufferPosition-1,&IoResult,&lpClientContext->Overlapped);
					LastError = (int) GetLastError();
					if (!Result && LastError == ERROR_IO_PENDING)
					{
						// Still waiting for more data to be received from client
/*						OverlappedResult = GetOverlappedResult((HANDLE) lpClientContext->Socket,&lpClientContext->Overlapped,&IoResult,TRUE);
						if (!OverlappedResult)
						{
							// Failed I/O operation
							lpClientContext->LastError = SocketError(lpClientContext);
							sprintf_s(Buffer,sizeof(Buffer),"GetOverlappedResult() failed with WSA error %ld for ID %ld",(long) lpClientContext->LastError,lpClientContext->ConnectionID);
							UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
							CloseClient(lpClientContext,FALSE);
						}
						#ifdef TESTING_PROCESS_LOGGING
						else
						{
							sprintf_s(Buffer,sizeof(Buffer),"GetOverlappedResult() found %ld bytes for ID %ld",(long) IoResult,lpClientContext->ConnectionID);
							UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
						}
						#endif
*/					}
					else if (!Result && LastError != ERROR_IO_PENDING)
					{
						if (LastError == ERROR_INVALID_HANDLE)
						{
							_time64(&lpClientContext->LastAccess);
							lpClientContext->CurrentState = STATE_QUIT;
							lpClientContext->LastError = WSAECONNRESET;
							lpClientContext->SafeToDelete = TRUE;
							lpClientContext->ThreadExited = TRUE;
						}
						else
						{
							sprintf_s(Buffer,sizeof(Buffer),"Failed to read data from connection with socket error %ld for ID %ld",(long) lpClientContext->LastError,lpClientContext->ConnectionID);
							UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
						}
						CloseClient(lpClientContext,FALSE);
						continue;
					}
					#ifdef TESTING_PROCESS_LOGGING
					else if (Result)
					{
						sprintf_s(Buffer,sizeof(Buffer),"ReadFile() accepted %ld bytes for ID %ld",(long) IoResult,lpClientContext->ConnectionID);
						UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					}
					#endif
				}
			}
		}
		if (SharedThreads && (ServiceTerminating || lpClientContext->CurrentState == STATE_QUIT))
		{
			if (!lpClientContext->ThreadExited)
			{
				#ifdef TESTING_PROCESS_LOGGING
				if (ServiceTerminating)
				{
					sprintf_s(Buffer,sizeof(Buffer),"Shutting down shared worker thread for ID %ld",lpClientContext->ConnectionID);
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
				}
				else
				{
					sprintf_s(Buffer,sizeof(Buffer),"Exiting shared worker thread for ID %ld",lpClientContext->ConnectionID);
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
				}
				#endif
				_time64(&lpClientContext->LastAccess);
				lpClientContext->SafeToDelete = TRUE;
				lpClientContext->ThreadExited = TRUE;
			}
			if (ServiceTerminating)
				return(0);
			else
				continue;
		}
		YieldControl();
	}
	#ifdef TESTING_PROCESS_LOGGING
	UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Shutting down worker thread unexpectedly");
	#endif
	_time64(&lpClientContext->LastAccess);
	lpClientContext->SafeToDelete = TRUE;
	lpClientContext->ThreadExited = TRUE;
	return(0);
}

int GetCommand(char *Data)
{
	char	CmdBuffer[5],NextCharExpected = '\r',NextCharExpected2 = '\n';
	BOOL	FollowingSpaceAllowed = TRUE;
	int		CommandFound = COMMAND_UNKNOWN;

	if (strlen(Data) >= 4)
	{
		CmdBuffer[0] = Data[0];
		CmdBuffer[1] = Data[1];
		CmdBuffer[2] = Data[2];
		CmdBuffer[3] = Data[3];
		CmdBuffer[4] = '\0';
		_strupr_s(CmdBuffer,sizeof(CmdBuffer));

		if (strcmp(CmdBuffer,"HELO") == 0)
			CommandFound = COMMAND_HELO;
		else if (strcmp(CmdBuffer,"EHLO") == 0)
			CommandFound = COMMAND_EHLO;
		else if (strcmp(CmdBuffer,"MAIL") == 0)
		{
			CommandFound = COMMAND_MAIL;
			NextCharExpected = ' ';
			NextCharExpected2 = ' ';
		}
		else if (strcmp(CmdBuffer,"RCPT") == 0)
		{
			CommandFound = COMMAND_RCPT;
			NextCharExpected = ' ';
			NextCharExpected2 = ' ';
		}
		else if (strcmp(CmdBuffer,"DATA") == 0)
			CommandFound = COMMAND_DATA;
		else if (strcmp(CmdBuffer,"HELP") == 0)
			CommandFound = COMMAND_HELP;
		else if (strcmp(CmdBuffer,"QUIT") == 0)
			CommandFound = COMMAND_QUIT;
		else if (strcmp(CmdBuffer,"EXIT") == 0)
			CommandFound = COMMAND_QUIT;
		else if (strcmp(CmdBuffer,"NOOP") == 0)
			CommandFound = COMMAND_NOOP;
		else if (strcmp(CmdBuffer,"RSET") == 0)
			CommandFound = COMMAND_RSET;
		else if (strcmp(CmdBuffer,"STAT") == 0)
			CommandFound = COMMAND_STAT;
		else if (strcmp(CmdBuffer,"KILL") == 0)
			CommandFound = COMMAND_KILL;
		else if (strcmp(CmdBuffer,"WLST") == 0)
			CommandFound = COMMAND_WLST;
		else if (strcmp(CmdBuffer,"BLST") == 0)
			CommandFound = COMMAND_BLST;
		else if (strcmp(CmdBuffer,"CTRK") == 0)
			CommandFound = COMMAND_CTRK;
		else if (strcmp(CmdBuffer,"LTRK") == 0)
			CommandFound = COMMAND_LTRK;
		else if (strcmp(CmdBuffer,"STRK") == 0)
			CommandFound = COMMAND_STRK;
		else if (strcmp(CmdBuffer,"HOLD") == 0)
			CommandFound = COMMAND_HOLD;
		else if (strcmp(CmdBuffer,"CSTA") == 0)
			CommandFound = COMMAND_CSTA;
		else if (strcmp(CmdBuffer,"COBK") == 0)
			CommandFound = COMMAND_COBK;
		else if (strcmp(CmdBuffer,"LCFG") == 0)
			CommandFound = COMMAND_LCFG;
		else if (strcmp(CmdBuffer,"VRFY") == 0)
			CommandFound = COMMAND_VRFY;
		else if (strcmp(CmdBuffer,"FROM") == 0)
		{
			CommandFound = COMMAND_FROM;
			NextCharExpected = ':';
			NextCharExpected2 = ':';
			FollowingSpaceAllowed = FALSE;
		}
		else if(strncmp(CmdBuffer,"TO:",3) == 0)
			CommandFound = COMMAND_TO;

		if (CommandFound != COMMAND_TO)
		{
			if (CommandFound != COMMAND_UNKNOWN && Data[4] != NextCharExpected && Data[4] != NextCharExpected2)
			{
				if (!FollowingSpaceAllowed)
					CommandFound = COMMAND_UNKNOWN;
				else if (FollowingSpaceAllowed && Data[4] != ' ')
					CommandFound = COMMAND_UNKNOWN;
			}
		}
	}
	return(CommandFound);
}

BOOL CommandLenError(int Command,char *Data)
{
	BOOL	Result = FALSE;
	int		MaxLength = BUFFER_SIZE-1,CommandLen = 0;

	if (Command != COMMAND_UNKNOWN)
	{
		switch (Command)
		{
			case COMMAND_HELO:		MaxLength = COMMAND_HELO_LEN;
									break;
			case COMMAND_EHLO:		MaxLength = COMMAND_EHLO_LEN;
									break;
			case COMMAND_MAIL:		MaxLength = COMMAND_MAIL_LEN;
									break;
			case COMMAND_RCPT:		MaxLength = COMMAND_RCPT_LEN;
									break;
			case COMMAND_DATA:		MaxLength = COMMAND_DATA_LEN;
									break;
			case COMMAND_HELP:		MaxLength = COMMAND_HELP_LEN;
									break;
			case COMMAND_QUIT:		MaxLength = COMMAND_QUIT_LEN;
									break;
			case COMMAND_NOOP:		MaxLength = COMMAND_NOOP_LEN;
									break;
			case COMMAND_RSET:		MaxLength = COMMAND_RSET_LEN;
									break;
			case COMMAND_STAT:		MaxLength = COMMAND_STAT_LEN;
									break;
			case COMMAND_KILL:		MaxLength = COMMAND_KILL_LEN;
									break;
			case COMMAND_WLST:		MaxLength = COMMAND_WLST_LEN;
									break;
			case COMMAND_BLST:		MaxLength = COMMAND_BLST_LEN;
									break;
			case COMMAND_CTRK:		MaxLength = COMMAND_CTRK_LEN;
									break;
			case COMMAND_LTRK:		MaxLength = COMMAND_LTRK_LEN;
									break;
			case COMMAND_STRK:		MaxLength = COMMAND_STRK_LEN;
									break;
			case COMMAND_HOLD:		MaxLength = COMMAND_HOLD_LEN;
									break;
			case COMMAND_CSTA:		MaxLength = COMMAND_CSTA_LEN;
									break;
			case COMMAND_COBK:		MaxLength = COMMAND_COBK_LEN;
									break;
			case COMMAND_LCFG:		MaxLength = COMMAND_LCFG_LEN;
									break;
			case COMMAND_VRFY:		MaxLength = COMMAND_VRFY_LEN;
									break;
			case COMMAND_FROM:		MaxLength = COMMAND_FROM_LEN;
									break;
			case COMMAND_TO:		MaxLength = COMMAND_TO_LEN;
									break;
		}

		// Ignore any trailing non-space characters
		CommandLen = (int) strlen(Data);
		while (CommandLen > 0 && (Data[CommandLen-1] == ' ' || Data[CommandLen-1] == '\t' || Data[CommandLen-1] == '\r' || Data[CommandLen-1] == '\n'))
			CommandLen--;
		if (CommandLen > MaxLength)
			Result = TRUE;
	}
	return(Result);
}

BOOL ValidAddress(char *Address)
{
	BOOL	Result = TRUE;
	int		AtCount = 0,PeriodCount = 0;
	char	*Pointer,*FirstChar,*LastChar,*PrevChar,*NextChar;

	Pointer = Address;
	FirstChar = Pointer;
	LastChar = Pointer;
	PrevChar = Pointer;
	NextChar = Pointer+1;
	while (Result && *Pointer != '\0' && *Pointer != '\r' && *Pointer != '\n')
	{
		LastChar = Pointer;
		if (*Pointer == '@')
		{
			// Do not allow a period to be right before or right after the at sign
			if (PrevChar != Pointer && *PrevChar == '.')
				Result = FALSE;
			if (NextChar != Pointer && *NextChar == '.')
				Result = FALSE;
			AtCount++;
		}
		if (*Pointer == '.' && AtCount > 0)
			PeriodCount++;
		if (*Pointer == '\t' || *Pointer == ':' || *Pointer == ';' || *Pointer == '<' || *Pointer == '>' || *Pointer == '[' || *Pointer == ']' || *Pointer == '(' || *Pointer == ')' || *Pointer == ',' || *Pointer == ' ' || *Pointer == 34)
			Result = FALSE;
		PrevChar = Pointer;
		Pointer++;
		NextChar = Pointer+1;
	}
	if (Result && (AtCount != 1 || PeriodCount < 1 || *FirstChar == '@' || *LastChar == '@' || *FirstChar == '.' || *LastChar == '.'))
		Result = FALSE;
	return(Result);
}

BOOL LocalAddress(char *Address,char *ConnectionAddress)
{
	BOOL			Result = FALSE,IPConverted;
	FILTER_ENTRY	*Position = NULL;
	char			*DomainPosition = NULL;
	int				IPNum1,IPNum2,IPNum3,IPNum4;

	if (LocalFilters != NULL)
	{
		IPConverted = ConvertIPString(ConnectionAddress,&IPNum1,&IPNum2,&IPNum3,&IPNum4);
		if (strlen(Address) > 0)
		{
			DomainPosition = &Address[strlen(Address)-1];
			while (DomainPosition >= Address && *DomainPosition != '@')
				DomainPosition--;
			if (DomainPosition >= Address && *DomainPosition == '@')
				DomainPosition++;
		}
		EnterCriticalSection(&LocalCriticalSection);
		LocalAccessCount++;
		LeaveCriticalSection(&LocalCriticalSection);
		Position = LocalFilters;
		while (!Result && Position != NULL)
		{
			if (Position->Filter[0] == '0')
			{
				// IP Range
				if (IPConverted && IPInSubnet((unsigned char) Position->Filter[2],(unsigned char) Position->Filter[3],(unsigned char) Position->Filter[4],(unsigned char) Position->Filter[5],(unsigned char) Position->Filter[6],(unsigned char) Position->Filter[7],(unsigned char) Position->Filter[8],(unsigned char) Position->Filter[9],IPNum1,IPNum2,IPNum3,IPNum4))
					Result = TRUE;
			}
			else if (Position->Filter[0] != '0' && DomainPosition != NULL)
			{
				// Domain
				if (strlen(DomainPosition) > 0 && _stricmp(&Position->Filter[2],DomainPosition) == 0)
					Result = TRUE;
			}
			Position = (FILTER_ENTRY *) Position->pvNext;
		}
		EnterCriticalSection(&LocalCriticalSection);
		LocalAccessCount--;
		LeaveCriticalSection(&LocalCriticalSection);
	}
	return(Result);
}

BOOL WhiteListIP(char *ConnectionAddress)
{
	BOOL			Result = FALSE,IPConverted;
	int				IPNum1,IPNum2,IPNum3,IPNum4;
	FILTER_ENTRY	*FilterList;

	if (DomainFilters != NULL)
	{
		IPConverted = ConvertIPString(ConnectionAddress,&IPNum1,&IPNum2,&IPNum3,&IPNum4);
		EnterCriticalSection(&DomainCriticalSection);
		DomainAccessCount++;
		LeaveCriticalSection(&DomainCriticalSection);
		FilterList = DomainFilters;
		while (!Result && FilterList != NULL)
		{
			// Check only IP addresses
			if (FilterList->Filter[1] == '0')
				if (IPInSubnet((unsigned char) FilterList->Filter[4],(unsigned char) FilterList->Filter[5],(unsigned char) FilterList->Filter[6],(unsigned char) FilterList->Filter[7],(unsigned char) FilterList->Filter[8],(unsigned char) FilterList->Filter[9],(unsigned char) FilterList->Filter[10],(unsigned char) FilterList->Filter[11],IPNum1,IPNum2,IPNum3,IPNum4))
					if (FilterList->Filter[0] == '0')
						Result = TRUE;
			FilterList = (FILTER_ENTRY *) FilterList->pvNext;
		}
		EnterCriticalSection(&DomainCriticalSection);
		DomainAccessCount--;
		LeaveCriticalSection(&DomainCriticalSection);
	}
	return(Result);
}

int SendHelp(CLIENT_CONTEXT *lpClientContext)
{
	char	Buffer[MAX_WORK_BUFFER_SIZE];
	int		Error;

	sprintf_s(Buffer,sizeof(Buffer),"214-Server Commands:\r\n");
	strcat_s(Buffer,sizeof(Buffer),"214-   HELO   EHLO   MAIL   RCPT   DATA   HELP   NOOP\r\n");
	strcat_s(Buffer,sizeof(Buffer),"214-   RSET   VRFY   QUIT   EXIT   STAT   CSTA   LCFG\r\n");
	strcat_s(Buffer,sizeof(Buffer),"214-   CTRK   LTRK   STRK   HOLD   KILL   WLST   BLST\r\n");
	strcat_s(Buffer,sizeof(Buffer),"214-   COBK\r\n");
	strcat_s(Buffer,sizeof(Buffer),"214 End of help info\r\n");
	Error = SendData(lpClientContext,Buffer,strlen(Buffer));
	return(Error);
}

char *SearchAndReplace(char *InputBuffer,char *SearchFor,char *ReplaceWith,int *ReplacementCount)
{
	int		Loop,Loop2,InputLen,SearchLen,ReplaceLen;

	InputLen = strlen(InputBuffer);
	SearchLen = strlen(SearchFor);
	ReplaceLen = strlen(ReplaceWith);
	for (Loop = 0; Loop < InputLen; Loop++)
		if (_strnicmp(&InputBuffer[Loop],SearchFor,SearchLen) == 0)
		{
			if (ReplacementCount != NULL)
				(*ReplacementCount)++;
			if (SearchLen > ReplaceLen)
			{
				for (Loop2 = Loop; Loop2 <= InputLen-(SearchLen-ReplaceLen); Loop2++)
					InputBuffer[Loop2] = InputBuffer[Loop2+(SearchLen-ReplaceLen)];
				InputLen -= SearchLen-ReplaceLen;
			}
			else if (SearchLen < ReplaceLen)
			{
				InputBuffer[InputLen+(ReplaceLen-SearchLen)] = '\0';
				for (Loop2 = InputLen-1; Loop2 > Loop; Loop2--)
					InputBuffer[Loop2+(ReplaceLen-SearchLen)] = InputBuffer[Loop2];
				InputLen += ReplaceLen-SearchLen;
			}
			for (Loop2 = 0; Loop2 < ReplaceLen; Loop2++)
			{
				InputBuffer[Loop] = ReplaceWith[Loop2];
				Loop++;
			}
			Loop--;
		}
	return(InputBuffer);
}

int SendData(CLIENT_CONTEXT *lpClientContext,char *SendString,int StringLength)
{
	int		Error = 0;
	char	Buffer[BUFFER_SIZE];

	if (lpClientContext == NULL || !lpClientContext->SocketOpen || lpClientContext->Socket == INVALID_SOCKET)
		Error = 1;
	else
		Error = lpClientContext->LastError;
	if (Error == 0)
	{
		strncpy_s(Buffer,sizeof(Buffer),SendString,StringLength);
		Buffer[StringLength] = '\0';
		if (StringLength > 0 && !lpClientContext->Timeout && !lpClientContext->TerminationMessage)
		{
			#ifdef TESTING_DETAILED_LOGGING
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Sending data");
			#endif
			lpClientContext->SendComplete = FALSE;
			_time64(&lpClientContext->LastAccess);
			Error = ::send(lpClientContext->Socket,Buffer,StringLength,0);
			if (Error == SOCKET_ERROR)
			{
				lpClientContext->LastError = SocketError(lpClientContext);
				CheckSocketError(lpClientContext);
				if (lpClientContext->LastError != WSAECONNRESET && lpClientContext->LastError != 0)
				{
					sprintf_s(Buffer,sizeof(Buffer),"Failed to send data with WSA error %ld",(long) lpClientContext->LastError);
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
				}
				CloseClient(lpClientContext,FALSE);
			}
			lpClientContext->SendComplete = TRUE;
			_time64(&lpClientContext->LastAccess);
		}
	}
	return(Error);
}

void CheckSocketError(CLIENT_CONTEXT *lpClientContext)
{
	char		Buffer[MAX_WORK_BUFFER_SIZE];

	if (lpClientContext != NULL)
		if (lpClientContext->LastError != 0)
		{
			sprintf_s(Buffer,sizeof(Buffer),"Detected error %ld on socket for ID %ld",lpClientContext->LastError,lpClientContext->ConnectionID);
			#ifdef TESTING_PROCESS_LOGGING
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
			#endif
		}
}

void CloseClient(CLIENT_CONTEXT *lpClientContext,BOOL bGraceful)
{
	#ifdef TESTING_PROCESS_LOGGING
	char		Buffer[MAX_WORK_BUFFER_SIZE];
	#endif

	if (lpClientContext != NULL)
	{
		switch (lpClientContext->LastError)
		{
			case WSAECONNRESET:
			case WSAETIMEDOUT:
			case WSAEINTR:
			case WAIT_TIMEOUT:
			case ERROR_OPERATION_ABORTED:
			case ERROR_FILE_NOT_FOUND:
			case ERROR_ALREADY_EXISTS:	// These errors occurs when a connection times out
										bGraceful = FALSE;
										break;
			case WSANOTINITIALISED:
			case WSAENETDOWN:
			case WSAEFAULT:
			case WSAENETRESET:
			case WSAENOBUFS:
			case WSAENOTCONN:
			case WSAENOTSOCK:
			case WSAEOPNOTSUPP:
			case WSAESHUTDOWN:
			case WSAEWOULDBLOCK:
			case WSAEMSGSIZE:
			case WSAEHOSTUNREACH:
			case WSAEINVAL:
			case WSAECONNABORTED:
			case ERROR_NETNAME_DELETED:
			case ERROR_INVALID_HANDLE:
			case ERROR_NOT_ENOUGH_MEMORY:
			case ERROR_NOT_READY:
			case ERROR_CRC:
			case ERROR_GEN_FAILURE:
			case ERROR_REM_NOT_LIST:
			case ERROR_DEV_NOT_EXIST:
			case ERROR_UNEXP_NET_ERR:
			case ERROR_BAD_DEV_TYPE:
			case ERROR_BAD_NET_NAME:
			case ERROR_EA_ACCESS_DENIED:
			case ERROR_IO_INCOMPLETE:
			case ERROR_NOACCESS:
										UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Critical error.  Terminating connection.");
										bGraceful = FALSE;
										break;
		}
		if (bGraceful)
			Sleep(100);
		if (lpClientContext->FileOpen && lpClientContext->CurrentState == STATE_DATA && (lpClientContext->MessageSize > 0 || lpClientContext->BufferPosition > 0))
		{
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Message is incomplete");
			lpClientContext->MessageIncomplete = TRUE;
			if (lpClientContext->BufferPosition > 0 && lpClientContext->BufferPosition < sizeof(lpClientContext->Buffer))
			{
				lpClientContext->Buffer[lpClientContext->BufferPosition] = '\0';
				lpClientContext->MessageSize += strlen(lpClientContext->Buffer);
				if (lpClientContext->FileOpen)
					fprintf(lpClientContext->MessageFile,"%s",lpClientContext->Buffer);
			}
			if (lpClientContext->FileOpen)
			{
				fclose(lpClientContext->MessageFile);
				lpClientContext->FileOpen = FALSE;
			}
			lpClientContext->BufferPosition = 0;
			memset(lpClientContext->Buffer,0,sizeof(lpClientContext->Buffer));
			lpClientContext->CurrentState = STATE_PROCESS;
		}
		else if (lpClientContext->CurrentState != STATE_PROCESS && lpClientContext->CurrentState != STATE_FORWARD)
		{
			lpClientContext->CurrentState = STATE_QUIT;
			_time64(&lpClientContext->LastAccess);
			lpClientContext->SafeToDelete = TRUE;
		}
		if (lpClientContext->HostSocketOpen)
		{
			lpClientContext->HostSocketOpen = FALSE;
			if (lpClientContext->HostSocket != INVALID_SOCKET)
			{
				::shutdown(lpClientContext->HostSocket,SD_BOTH);
				::closesocket(lpClientContext->HostSocket);
				lpClientContext->HostSocket = INVALID_SOCKET;
			}
		}
		if (lpClientContext->SocketOpen)
		{
			#ifdef TESTING_PROCESS_LOGGING
			sprintf_s(Buffer,sizeof(Buffer),"Closing connection for ID %ld",lpClientContext->ConnectionID);
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
			#endif
			if (SharedThreads)
			{
				if (lpClientContext->SocketOpen && lpClientContext->Socket != INVALID_SOCKET && !bGraceful)
				{
					#ifdef TESTING_PROCESS_LOGGING
					sprintf_s(Buffer,sizeof(Buffer),"CloseClient() cancelling I/O on socket, currently %s",(lpClientContext->SendComplete ? "receiving" : "sending"));
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					#endif
					CancelIo((HANDLE) lpClientContext->Socket);
				}
				if (lpClientContext->HostSocketOpen && lpClientContext->HostSocket != INVALID_SOCKET)
				{
					#ifdef TESTING_PROCESS_LOGGING
					sprintf_s(Buffer,sizeof(Buffer),"CloseClient() cancelling I/O on host host socket, currently %s",(lpClientContext->SendComplete ? "receiving" : "sending"));
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					#endif
					CancelIo((HANDLE) lpClientContext->HostSocket);
				}
			}
			lpClientContext->SocketOpen = FALSE;
			if (lpClientContext->Socket != INVALID_SOCKET)
			{
				if (::shutdown(lpClientContext->Socket,SD_BOTH) != 0 && lpClientContext->LastError == 0)
				{
					lpClientContext->LastError = SocketError(lpClientContext);
					CheckSocketError(lpClientContext);
					#ifdef TESTING_PROCESS_LOGGING
					sprintf_s(Buffer,sizeof(Buffer),"CloseClient()->shutdown recorded socket error of %ld",(long) lpClientContext->LastError);
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					#endif
				}
				if (::closesocket(lpClientContext->Socket) != 0 && lpClientContext->LastError == 0)
				{
					lpClientContext->LastError = SocketError(lpClientContext);
					CheckSocketError(lpClientContext);
					#ifdef TESTING_PROCESS_LOGGING
					sprintf_s(Buffer,sizeof(Buffer),"CloseClient()->closesocket recorded socket error of %ld",(long) lpClientContext->LastError);
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
					#endif
				}
				lpClientContext->Socket = INVALID_SOCKET;
			}
		}
	}
}

BOOL ProcessFilter(CLIENT_CONTEXT *lpClientContext)
{
	DWORD			IoSize,Position;
	char			HeaderItem[MAX_KEYWORD_SIZE],HeaderValue[MAX_KEYVALUE_SIZE+5],Buffer[MAX_KEYWORD_SIZE];
	int				HeaderPosition,Loop,MimeEncodedBase = 64,Length,Num1,Num2,Num3,Num4;
	HOSTENT			*HostComputer;
	BOOL			Result = TRUE,FileFailure = FALSE,AddressElement,AllSpaces,FoundBreak,FoundQuote,IPWhiteList,LookedForSubject = FALSE;
	BOOL			HeaderSection,TextSection = TRUE,PlainText = TRUE,ReadingBody = FALSE,MimeVersionFound = FALSE,MimeEncoded = FALSE,UUEncoded = FALSE,CharTranslation = FALSE;

	#ifdef TESTING_PROCESS_LOGGING
	UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Starting ProcessFilter()");
	#endif
	lpClientContext->ProcessFilterExecuted = TRUE;
	lpClientContext->WhiteList = FALSE;
	lpClientContext->ScanStep = 0;
	lpClientContext->ScanSize = 0;
	lpClientContext->ScanPosition = 0;
	lpClientContext->CharReplacements = 0;
	lpClientContext->HTMLAddrCount = 0;
	memset(lpClientContext->StepsTaken,0,sizeof(lpClientContext->StepsTaken));
	lpClientContext->HTMLLinks = 0;
	lpClientContext->HTMLLinksResolved = 0;
	if (!lpClientContext->WhiteList && !lpClientContext->PermBlackList && lpClientContext->BlackListType != BL_TAG && lpClientContext->BlackListType != BL_FORMAT)
	{
		lpClientContext->BlackListType = BL_NONE;
		lpClientContext->BlackListSubType = BL_SUB_TOTAL;
		lpClientContext->BlackListResult = FormatErrors;
		lpClientContext->WhiteRecipient = -1;
		lpClientContext->SuspectDomain = FALSE;
		lpClientContext->SuspectResult = FormatErrors;
		memset(lpClientContext->FilteredBy,0,sizeof(lpClientContext->FilteredBy));
	}
	IPWhiteList = FALSE;
	if (Result && ContinueProcess(lpClientContext,TRUE))
	{
		// Check IP address of connection
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = '1';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step 1",lpClientContext->FilteredBy);
		#endif
		CheckIPFilter(lpClientContext);
		IPWhiteList = lpClientContext->WhiteList;
	}
	if (Result && ContinueProcess(lpClientContext,TRUE) && OutbreakCheck && !LocalAddress("",lpClientContext->AddressString) && !lpClientContext->WhiteList && !lpClientContext->PermBlackList)
	{
		// Check connection IP against outbreak filters
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = '+';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step +1",lpClientContext->FilteredBy);
		#endif
		CheckOutbreakFilter(lpClientContext);

		// Check for suspect recipients
		for (Loop = 0; Loop < lpClientContext->RCPTCount && ContinueProcess(lpClientContext,TRUE); Loop++)
			CheckSuspectRecipients(lpClientContext,lpClientContext->RCPTAddress[Loop]);
	}

	// Check for white list recipients
	for (Loop = 0; lpClientContext->WhiteRecipient < 0 && Loop < lpClientContext->RCPTCount; Loop++)
		CheckWhiteListRecipients(lpClientContext,lpClientContext->RCPTAddress[Loop],Loop);

	if (Result && ContinueProcess(lpClientContext,TRUE) && strlen(lpClientContext->MAILAddress) > 0)
	{
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = '2';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step 2",lpClientContext->FilteredBy);
		#endif
		CheckDomainFilter(lpClientContext,lpClientContext->MAILAddress,(lpClientContext->SuspectDomain ? NULL : &lpClientContext->SuspectDomain),(lpClientContext->SuspectDomain ? NULL : &lpClientContext->SuspectResult),BL_SUB_DOMAIN_ADDRESS);
	}
	if (Result && (ContinueProcess(lpClientContext,TRUE) || AlternateRouting > 0))
	{
		#ifdef TESTING_USE_TEMP_FILE
		lpClientContext->MessageSize = MAX_MESSAGE_SIZE;
		strcpy_s(lpClientContext->FileName,sizeof(lpClientContext->FileName),"1-Mail.for.test33");
		sprintf_s(lpClientContext->FullFileName,sizeof(lpClientContext->FullFileName),"C:\\PROJECTS\\SMTPserv\\temp\\%s",lpClientContext->FileName);
		sprintf_s(lpClientContext->TurfFileName,sizeof(lpClientContext->TurfFileName),"C:\\PROJECTS\\SMTPserv\\TurfDir\\%s",lpClientContext->FileName);
		#endif
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = '3';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step 3",lpClientContext->FilteredBy);
		#endif
		if (!lpClientContext->FileOpen && fopen_s(&lpClientContext->MessageFile,lpClientContext->FullFileName,"rb") == 0)
		{
			lpClientContext->FileOpen = TRUE;
			lpClientContext->MultiPartMessage = FALSE;
			lpClientContext->EmptyMessage = TRUE;
			MimeEncoded = FALSE;
			MimeEncodedBase = 64;
			UUEncoded = FALSE;
			MimeVersionFound = FALSE;
			CharTranslation = FALSE;
			TextSection = TRUE;
			PlainText = TRUE;
			HeaderSection = TRUE;
			memset(HeaderItem,0,sizeof(HeaderItem));
			memset(HeaderValue,0,sizeof(HeaderValue));
			while (Result && (ContinueProcess(lpClientContext,TRUE) || AlternateRouting > 0) && !FileFailure && !feof(lpClientContext->MessageFile))
			{
				IoSize = fread(lpClientContext->Buffer,sizeof(char),sizeof(lpClientContext->Buffer),lpClientContext->MessageFile);
				if ((long) IoSize > 0)
				{
					Position = 0;
					while ((long) Position < (long) IoSize)
					{
						// Make sure there aren't any NULL characters to screw things up
						if (lpClientContext->Buffer[Position] == '\0')
							lpClientContext->Buffer[Position] = ' ';
						Position++;
					}
					Position = 0;
					while ((long) Position < (long) IoSize)
					{
						while (HeaderSection && (long) Position < (long) IoSize)
						{
							// Extract header elements
							Position += ExtractHeaderElement(&lpClientContext->Buffer[Position],(long) IoSize-Position,HeaderItem,MAX_KEYWORD_SIZE,HeaderValue,MAX_KEYVALUE_SIZE,&AllSpaces);
							if ((long) Position < (long) IoSize && (strlen(HeaderItem) > 0 || strlen(HeaderValue) > 0) && !AllSpaces)
							{
								// Record header information
								if (FindString(HeaderItem,"Content-Type",SEARCH_CONTAINS))
								{
									TextSection = FindString(HeaderValue,"text/",SEARCH_CONTAINS);
									if (!TextSection)
										TextSection = (_stricmp(HeaderValue,"text") == 0 ? TRUE : FALSE);
									if (!TextSection)
										TextSection = FindString(HeaderValue,"message/rfc822",SEARCH_CONTAINS);
									PlainText = FindString(HeaderValue,"text/plain",SEARCH_CONTAINS);
									PlainText = FindString(HeaderValue,"text/rfc822-headers",SEARCH_CONTAINS);
									PlainText = FindString(HeaderValue,"message/rfc822",SEARCH_CONTAINS);
									if (lpClientContext->EmptyMessage && !TextSection)
										lpClientContext->EmptyMessage = FALSE;
								}
								if (FindString(HeaderItem,"Content-Type",SEARCH_EXACT) && FindString(HeaderValue,"multipart",SEARCH_CONTAINS) && FindString(HeaderValue,"boundary",SEARCH_CONTAINS))
								{
									// This must be a multipart message
									lpClientContext->MultiPartMessage = TRUE;
									TextSection = TRUE;
									PlainText = TRUE;
									HeaderPosition = 0;
									while (HeaderPosition < (int) strlen(HeaderValue) && !FindString(&HeaderValue[HeaderPosition],"boundary",SEARCH_PREFIX))
										HeaderPosition++;
									HeaderPosition += 8;
									FoundBreak = FALSE;
									FoundQuote = FALSE;
									while (!FoundBreak && HeaderPosition < (int) strlen(HeaderValue))
									{
										if (HeaderValue[HeaderPosition] == ' ' || HeaderValue[HeaderPosition] == '=')
											HeaderPosition++;
										else
										{
											FoundBreak = TRUE;
											if (HeaderValue[HeaderPosition] == '\"')
											{
												HeaderPosition++;
												FoundQuote = TRUE;
											}
										}
									}
									if (strlen(&HeaderValue[HeaderPosition]) >= sizeof(HeaderItem))
									{
										strncpy_s(HeaderItem,sizeof(HeaderItem),&HeaderValue[HeaderPosition],sizeof(HeaderItem)-1);
										HeaderItem[sizeof(HeaderItem)-1] = '\0';
									}
									else
										strcpy_s(HeaderItem,sizeof(HeaderItem),&HeaderValue[HeaderPosition]);
									FoundBreak = FALSE;
									HeaderPosition = 0;
									while (!FoundBreak && HeaderPosition < (int) strlen(HeaderItem))
									{
										if (FoundQuote && HeaderItem[HeaderPosition] != '\"')
											HeaderPosition++;
										else if (!FoundQuote && HeaderItem[HeaderPosition] != ' ')
											HeaderPosition++;
										else
											FoundBreak = TRUE;
									}
									HeaderItem[HeaderPosition] = '\0';
									lpClientContext->CurrentBoundary = 0;
									sprintf_s(lpClientContext->Boundary[lpClientContext->CurrentBoundary],sizeof(lpClientContext->Boundary[lpClientContext->CurrentBoundary]),"--%s",HeaderItem);
									#ifdef TESTING_HEADER_LOGGING
									UpdateLogFile("Boundary","Definition",lpClientContext->Boundary[lpClientContext->CurrentBoundary]);
									#endif
								}
								else if (FindString(HeaderItem,"Content-Type",SEARCH_EXACT) && FindString(HeaderValue,"multipart",SEARCH_CONTAINS) && !FindString(HeaderValue,"boundary",SEARCH_CONTAINS))
								{
									TextSection = TRUE;
									PlainText = TRUE;
								}
								else if (FindString(HeaderItem,"MIME-Version",SEARCH_EXACT))
									MimeVersionFound = TRUE;
								else if (FindString(HeaderItem,"Content-Transfer-Encoding",SEARCH_CONTAINS))
								{
									if (FindString(HeaderValue,"Base64",SEARCH_CONTAINS) || FindString(HeaderValue,"6bit",SEARCH_CONTAINS) || FindString(HeaderValue,"6-bit",SEARCH_CONTAINS))
									{
										MimeEncoded = TRUE;
										MimeEncodedBase = 64;
									}
									if (FindString(HeaderValue,"Base32",SEARCH_CONTAINS) || FindString(HeaderValue,"5bit",SEARCH_CONTAINS) || FindString(HeaderValue,"5-bit",SEARCH_CONTAINS))
									{
										MimeEncoded = TRUE;
										MimeEncodedBase = 32;
									}
									if (FindString(HeaderValue,"Base16",SEARCH_CONTAINS) || FindString(HeaderValue,"4bit",SEARCH_CONTAINS) || FindString(HeaderValue,"4-bit",SEARCH_CONTAINS) || FindString(HeaderValue,"Hex",SEARCH_CONTAINS))
									{
										MimeEncoded = TRUE;
										MimeEncodedBase = 16;
									}
									CharTranslation = FindString(HeaderValue,"quoted-printable",SEARCH_CONTAINS);
								}
								else if (FindString(HeaderItem,"Subject",SEARCH_EXACT))
								{
									if (strlen(HeaderValue) >= sizeof(lpClientContext->SubjectLine))
									{
										strncpy_s(lpClientContext->SubjectLine,sizeof(lpClientContext->SubjectLine),HeaderValue,sizeof(lpClientContext->SubjectLine)-1);
										lpClientContext->SubjectLine[sizeof(lpClientContext->SubjectLine)-1] = '\0';
									}
									else
										strcpy_s(lpClientContext->SubjectLine,sizeof(lpClientContext->SubjectLine),HeaderValue);
									#ifdef TESTING_HEADER_LOGGING
									UpdateLogFile("SubjectLine","-",lpClientContext->SubjectLine);
									#endif
									TranslateAnnotatedChars(lpClientContext->SubjectLine);
								}
								else if (!IPWhiteList)
								{
									// Check header elements that may contain return addresses
									AddressElement = FALSE;
									if (!AddressElement && FindString(HeaderItem,"Message-ID",SEARCH_CONTAINS))
									{
										AddressElement = TRUE;
										if (FindString(HeaderItem,"Message-ID",SEARCH_EXACT))
										{
											if (strlen(HeaderValue) >= sizeof(lpClientContext->MessageID))
											{
												strncpy_s(lpClientContext->MessageID,sizeof(lpClientContext->MessageID),HeaderValue,sizeof(lpClientContext->MessageID)-1);
												lpClientContext->MessageID[sizeof(lpClientContext->MessageID)-1] = '\0';
											}
											else
												strcpy_s(lpClientContext->MessageID,sizeof(lpClientContext->MessageID),HeaderValue);
										}
									}
									if (!AddressElement && FindString(HeaderItem,"Return-Path",SEARCH_CONTAINS))
										AddressElement = TRUE;
									if (!AddressElement && FindString(HeaderItem,"From",SEARCH_CONTAINS))
									{
										AddressElement = TRUE;
										if (FindString(HeaderItem,"From",SEARCH_EXACT))
										{
											// If multiple from lines that accept the first and ignore the rest
											if (strlen(lpClientContext->FromField) == 0)
											{
												if (strlen(HeaderValue) >= sizeof(lpClientContext->FromField))
												{
													strncpy_s(lpClientContext->FromField,sizeof(lpClientContext->FromField),HeaderValue,sizeof(lpClientContext->FromField)-1);
													lpClientContext->FromField[sizeof(lpClientContext->FromField)-1] = '\0';
												}
												else
													strcpy_s(lpClientContext->FromField,sizeof(lpClientContext->FromField),HeaderValue);
											}
											else
												AddressElement = FALSE;
										}
									}
									if (!AddressElement && FindString(HeaderItem,"Reply-To",SEARCH_CONTAINS))
									{
										if (!FindString(HeaderItem,"In-Reply-To",SEARCH_CONTAINS))
											AddressElement = TRUE;
									}
									if (!AddressElement && FindString(HeaderItem,"Sender",SEARCH_CONTAINS))
										AddressElement = TRUE;
									if (!AddressElement && FindString(HeaderItem,"Unsubscribe",SEARCH_CONTAINS))
										AddressElement = TRUE;
									if (!AddressElement && FindString(HeaderItem,"Return-Receipt-To",SEARCH_CONTAINS))
										AddressElement = TRUE;
									if (!AddressElement && FindString(HeaderItem,"Errors-to",SEARCH_CONTAINS))
										AddressElement = TRUE;
									if (AddressElement)
										CheckDomainFilter(lpClientContext,HeaderValue,(lpClientContext->SuspectDomain ? NULL : &lpClientContext->SuspectDomain),(lpClientContext->SuspectDomain ? NULL : &lpClientContext->SuspectResult),BL_SUB_DOMAIN_ADDRESS);

									for (Loop = 0; ContinueProcess(lpClientContext,FALSE) && Loop < RejectTagCount; Loop++)
										if (strlen(RejectTagsPtr[Loop]) > 0 && FindString(HeaderItem,RejectTagsPtr[Loop],SEARCH_CONTAINS))
										{
											lpClientContext->BlackListType = BL_TAG;
											lpClientContext->BlackListSubType = BL_SUB_TAG_HEADER;
											sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"%s Tag",HeaderItem);
											lpClientContext->BlackListResult = FormatErrors;
										}
								}
							}
							else if ((long) Position < (long) IoSize)
							{
								HeaderSection = FALSE;
								ReadingBody = TRUE;
								lpClientContext->EmptyMessage = FALSE;

								if (!IPWhiteList && (lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListResult == BL_RESULT_FORWARD))
								{
									ExtractAddress(lpClientContext->FromField,HeaderItem,sizeof(HeaderItem),FALSE);
									if (RejectIfFromInvalid && !lpClientContext->WhiteList && !lpClientContext->PermBlackList && (strlen(lpClientContext->FromField) <= 0 || !ValidAddress(HeaderItem)))
									{
										// Invalid return addresses in the FROM: field are considered spam
										lpClientContext->BlackListType = BL_FORMAT;
										lpClientContext->BlackListSubType = BL_SUB_FORMAT_FROM;
										sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"Invalid From: %s",lpClientContext->FromField);
										lpClientContext->BlackListResult = FormatErrors;
									}
								}
							}
							if ((long) Position < (long) IoSize)
							{
								memset(HeaderItem,0,sizeof(HeaderItem));
								memset(HeaderValue,0,sizeof(HeaderValue));
							}
						}
						while (!HeaderSection && (long) Position < (long) IoSize)
						{
							// Translate body elements
							if (!IPWhiteList && lpClientContext->MessageBody == NULL)
							{
								lpClientContext->AllocatedSize = min(lpClientContext->MessageSize+1,MAX_MESSAGE_SIZE);
								#ifndef MEMORY_NEW_ALLOC
								lpClientContext->MessageBody = new char[lpClientContext->AllocatedSize];
								#else
								lpClientContext->MessageBody = (char *) AllocateBlock(lpClientContext->AllocatedSize,TRUE);
								#endif
								if (lpClientContext->MessageBody != NULL)
									memset(lpClientContext->MessageBody,0,lpClientContext->AllocatedSize);
								else
								{
									FileFailure = TRUE;
									UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Failed to allocate memory for message body scan");
								}
							}
							if (IPWhiteList || FileFailure || lpClientContext->MessageBody == NULL)
								Position = (long) IoSize;
							else
							{
								if (!ReadingBody)
								{
									// Read header elements of this section
									Position += ExtractHeaderElement(&lpClientContext->Buffer[Position],(long) IoSize-Position,HeaderItem,MAX_KEYWORD_SIZE,HeaderValue,MAX_KEYVALUE_SIZE,&AllSpaces);
									if (FindString(HeaderItem,"Content-Type",SEARCH_CONTAINS))
									{
										TextSection = FindString(HeaderValue,"text/",SEARCH_CONTAINS);
										if (!TextSection)
											TextSection = (_stricmp(HeaderValue,"text") == 0 ? TRUE : FALSE);
										if (!TextSection)
											TextSection = FindString(HeaderValue,"message/rfc822",SEARCH_CONTAINS);
										PlainText = FindString(HeaderValue,"text/plain",SEARCH_CONTAINS);
										PlainText = FindString(HeaderValue,"text/rfc822-headers",SEARCH_CONTAINS);
										PlainText = FindString(HeaderValue,"message/rfc822",SEARCH_CONTAINS);
										if (lpClientContext->EmptyMessage && !TextSection)
											lpClientContext->EmptyMessage = FALSE;
									}
									if (FindString(HeaderItem,"MIME-Version",SEARCH_EXACT))
										MimeVersionFound = TRUE;
									else if (FindString(HeaderItem,"Content-Transfer-Encoding",SEARCH_CONTAINS))
									{
										if (FindString(HeaderValue,"Base64",SEARCH_CONTAINS) || FindString(HeaderValue,"6bit",SEARCH_CONTAINS) || FindString(HeaderValue,"6-bit",SEARCH_CONTAINS))
										{
											MimeEncoded = TRUE;
											MimeEncodedBase = 64;
										}
										if (FindString(HeaderValue,"Base32",SEARCH_CONTAINS) || FindString(HeaderValue,"5bit",SEARCH_CONTAINS) || FindString(HeaderValue,"5-bit",SEARCH_CONTAINS))
										{
											MimeEncoded = TRUE;
											MimeEncodedBase = 32;
										}
										if (FindString(HeaderValue,"Base16",SEARCH_CONTAINS) || FindString(HeaderValue,"4bit",SEARCH_CONTAINS) || FindString(HeaderValue,"4-bit",SEARCH_CONTAINS) || FindString(HeaderValue,"Hex",SEARCH_CONTAINS))
										{
											MimeEncoded = TRUE;
											MimeEncodedBase = 16;
										}
										CharTranslation = FindString(HeaderValue,"quoted-printable",SEARCH_CONTAINS);
									}
									else if (FindString(HeaderItem,"Content-Type",SEARCH_EXACT) && FindString(HeaderValue,"multipart",SEARCH_CONTAINS) && FindString(HeaderValue,"boundary",SEARCH_CONTAINS) && lpClientContext->CurrentBoundary < MAX_BOUNDARIES-1)
									{
										// This must be a multipart message
										TextSection = TRUE;
										PlainText = TRUE;
										HeaderPosition = 0;
										while (HeaderPosition < (int) strlen(HeaderValue) && !FindString(&HeaderValue[HeaderPosition],"boundary",SEARCH_PREFIX))
											HeaderPosition++;
										HeaderPosition += 8;
										FoundBreak = FALSE;
										FoundQuote = FALSE;
										while (!FoundBreak && HeaderPosition < (int) strlen(HeaderValue))
										{
											if (HeaderValue[HeaderPosition] == ' ' || HeaderValue[HeaderPosition] == '=')
												HeaderPosition++;
											else
											{
												FoundBreak = TRUE;
												if (HeaderValue[HeaderPosition] == '\"')
												{
													HeaderPosition++;
													FoundQuote = TRUE;
												}
											}
										}
										if (strlen(&HeaderValue[HeaderPosition]) >= sizeof(HeaderItem))
										{
											strncpy_s(HeaderItem,sizeof(HeaderItem),&HeaderValue[HeaderPosition],sizeof(HeaderItem)-1);
											HeaderItem[sizeof(HeaderItem)-1] = '\0';
										}
										else
											strcpy_s(HeaderItem,sizeof(HeaderItem),&HeaderValue[HeaderPosition]);
										FoundBreak = FALSE;
										HeaderPosition = 0;
										while (!FoundBreak && HeaderPosition < (int) strlen(HeaderItem))
										{
											if (FoundQuote && HeaderItem[HeaderPosition] != '\"')
												HeaderPosition++;
											else if (!FoundQuote && HeaderItem[HeaderPosition] != ' ')
												HeaderPosition++;
											else
												FoundBreak = TRUE;
										}
										HeaderItem[HeaderPosition] = '\0';
										lpClientContext->CurrentBoundary++;
										sprintf_s(lpClientContext->Boundary[lpClientContext->CurrentBoundary],sizeof(lpClientContext->Boundary[lpClientContext->CurrentBoundary]),"--%s",HeaderItem);
										#ifdef TESTING_HEADER_LOGGING
										UpdateLogFile("Boundary","Definition",lpClientContext->Boundary[lpClientContext->CurrentBoundary]);
										#endif
									}
									else if (FindString(HeaderItem,"Content-Type",SEARCH_EXACT) && FindString(HeaderValue,"multipart",SEARCH_CONTAINS) && !FindString(HeaderValue,"boundary",SEARCH_CONTAINS))
									{
										TextSection = TRUE;
										PlainText = TRUE;
									}
									if (strlen(HeaderItem) == 0 && strlen(HeaderValue) == 0)
										ReadingBody = TRUE;
								}
								else
								{
									Position += ExtractBodyLine(&lpClientContext->Buffer[Position],(long) IoSize-Position,HeaderValue,MAX_KEYVALUE_SIZE,&AllSpaces);
									if (TextSection && FindString(HeaderValue,"Content-Transfer-Encoding: base",SEARCH_PREFIX))
									{
										// If this exact line is found in the message body then assume this is a poorly formatted bounce back message
										TextSection = FALSE;
										PlainText = FALSE;
										MimeEncoded = TRUE;
										MimeEncodedBase = 64;
										UUEncoded = FALSE;
										CharTranslation = FALSE;
										ReadingBody = FALSE;
										if (lpClientContext->CurrentBoundary < 0)
										{
											lpClientContext->CurrentBoundary++;
											memset(lpClientContext->Boundary[lpClientContext->CurrentBoundary],0,sizeof(lpClientContext->Boundary[lpClientContext->CurrentBoundary]));
										}
									}
									else if (lpClientContext->MultiPartMessage && lpClientContext->CurrentBoundary >= 0 && FindString(HeaderValue,lpClientContext->Boundary[lpClientContext->CurrentBoundary],SEARCH_PREFIX))
									{
										TextSection = TRUE;
										PlainText = TRUE;
										MimeEncoded = FALSE;
										MimeEncodedBase = 64;
										UUEncoded = FALSE;
										MimeVersionFound = FALSE;
										CharTranslation = FALSE;
										if (lpClientContext->CurrentBoundary >= 0 && HeaderValue[strlen(lpClientContext->Boundary[lpClientContext->CurrentBoundary])] == '-' && HeaderValue[strlen(lpClientContext->Boundary[lpClientContext->CurrentBoundary])+1] == '-')
										{
											#ifdef TESTING_HEADER_LOGGING
											UpdateLogFile("ProcessFilter()","Found","Boundary End");
											#endif
											// This denotes the end of the previous boundary group
											if (lpClientContext->CurrentBoundary > 0)
												lpClientContext->CurrentBoundary--;
											else
											{
												lpClientContext->EndOfMessageBoundary = TRUE;
												ReadingBody = FALSE;
												if ((int) strlen(lpClientContext->MessageBody) < lpClientContext->AllocatedSize-2)
													strcat_s(lpClientContext->MessageBody,lpClientContext->AllocatedSize,"\r\n");
											}
										}
										else
										{
											#ifdef TESTING_HEADER_LOGGING
											UpdateLogFile("ProcessFilter()","Found","Boundary");
											#endif
											ReadingBody = FALSE;
											if ((int) strlen(lpClientContext->MessageBody) < lpClientContext->AllocatedSize-2)
												strcat_s(lpClientContext->MessageBody,lpClientContext->AllocatedSize,"\r\n");
										}
									}
									else if (TextSection)
									{
										while (strlen(HeaderValue) > 0 && (HeaderValue[strlen(HeaderValue)-1] == ' ' || HeaderValue[strlen(HeaderValue)-1] == '\r' || HeaderValue[strlen(HeaderValue)-1] == '\n'))
											HeaderValue[strlen(HeaderValue)-1] = '\0';
										if (PlainText && !UUEncoded && !MimeEncoded && !MimeVersionFound && lpClientContext->CurrentBoundary < 0)
										{
											// Identify header of UUEncoded section
											if (FindString(HeaderValue,"begin ",SEARCH_PREFIX))
											{
												HeaderPosition = 6;
												while (HeaderValue[HeaderPosition] >= '0' && HeaderValue[HeaderPosition] <= '7')
													HeaderPosition++;
												if (HeaderValue[HeaderPosition] == ' ' && HeaderValue[HeaderPosition+1] != '\0')
												{
													UUEncoded = TRUE;
													#ifdef TESTING_HEADER_LOGGING
													UpdateLogFile("ProcessFilter()","Found","UUEncoded section beginning");
													#endif
												}
											}
										}
										if (UUEncoded)
										{
											UUEncoded = !FindString(HeaderValue,"end",SEARCH_EXACT);
											#ifdef TESTING_HEADER_LOGGING
											if (!UUEncoded)
												UpdateLogFile("ProcessFilter()","Found","UUEncoded section end");
											#endif
										}
										else
										{
											if (MimeEncoded)
												MimeDecodeLine(HeaderValue,MimeEncodedBase);
											if (CharTranslation)
											{
												HexDecodeLine(HeaderValue);
												if (strlen(HeaderValue) > 0 && HeaderValue[strlen(HeaderValue)-1] == '=')
													HeaderValue[strlen(HeaderValue)-1] = '\0';
												else
													strcat_s(HeaderValue,sizeof(HeaderValue)," ");
												if (HeaderValue[0] == '.' && HeaderValue[1] == '.')
													strcpy_s(HeaderValue,sizeof(HeaderValue),&HeaderValue[1]);
											}
											else if (!MimeEncoded)
												strcat_s(HeaderValue,sizeof(HeaderValue)," ");
											if ((int) strlen(lpClientContext->MessageBody)+(int) strlen(HeaderValue) < lpClientContext->AllocatedSize-1)
												strcat_s(lpClientContext->MessageBody,lpClientContext->AllocatedSize,HeaderValue);
										}
									}
								}
								if ((long) Position < (long) IoSize)
								{
									memset(HeaderItem,0,sizeof(HeaderItem));
									memset(HeaderValue,0,sizeof(HeaderValue));
								}
							}
						}
					}
				}
				else
				{
					FileFailure = TRUE;
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"ProcessFilter() Failed to read from file");
				}
			}
			fclose(lpClientContext->MessageFile);
			lpClientContext->FileOpen = FALSE;
		}
		else
		{
			Result = FALSE;
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"ProcessFilter() Failed to open file or file already open");
		}
	}
	if (strlen(lpClientContext->SubjectLine) > 0)
		LookedForSubject = TRUE;
	if (Result && !LookedForSubject)
	{
		// Extract only subject line from header
		LookedForSubject = TRUE;
		#ifdef TESTING_USE_TEMP_FILE
		lpClientContext->MessageSize = MAX_MESSAGE_SIZE;
		strcpy_s(lpClientContext->FileName,sizeof(lpClientContext->FileName),"1-Mail.for.test33");
		sprintf_s(lpClientContext->FullFileName,sizeof(lpClientContext->FullFileName),"C:\\PROJECTS\\SMTPserv\\temp\\%s",lpClientContext->FileName);
		sprintf_s(lpClientContext->TurfFileName,sizeof(lpClientContext->TurfFileName),"C:\\PROJECTS\\SMTPserv\\TurfDir\\%s",lpClientContext->FileName);
		#endif
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Extracting subject line only");
		#endif
		if (!lpClientContext->FileOpen && fopen_s(&lpClientContext->MessageFile,lpClientContext->FullFileName,"rb") == 0)
		{
			lpClientContext->FileOpen = TRUE;
			HeaderSection = TRUE;
			memset(HeaderItem,0,sizeof(HeaderItem));
			memset(HeaderValue,0,sizeof(HeaderValue));
			while (Result && HeaderSection && !FileFailure && !feof(lpClientContext->MessageFile))
			{
				IoSize = fread(lpClientContext->Buffer,sizeof(char),sizeof(lpClientContext->Buffer),lpClientContext->MessageFile);
				if ((long) IoSize > 0)
				{
					Position = 0;
					while ((long) Position < (long) IoSize)
					{
						// Make sure there aren't any NULL characters to screw things up
						if (lpClientContext->Buffer[Position] == '\0')
							lpClientContext->Buffer[Position] = ' ';
						Position++;
					}
					Position = 0;
					while (HeaderSection && (long) Position < (long) IoSize)
					{
						// Extract header elements
						Position += ExtractHeaderElement(&lpClientContext->Buffer[Position],(long) IoSize-Position,HeaderItem,MAX_KEYWORD_SIZE,HeaderValue,MAX_KEYVALUE_SIZE,&AllSpaces);
						if ((long) Position < (long) IoSize && (strlen(HeaderItem) > 0 || strlen(HeaderValue) > 0) && !AllSpaces)
						{
							// Record header information
							if (FindString(HeaderItem,"Subject",SEARCH_EXACT))
							{
								if (strlen(HeaderValue) >= sizeof(lpClientContext->SubjectLine))
								{
									strncpy_s(lpClientContext->SubjectLine,sizeof(lpClientContext->SubjectLine),HeaderValue,sizeof(lpClientContext->SubjectLine)-1);
									lpClientContext->SubjectLine[sizeof(lpClientContext->SubjectLine)-1] = '\0';
								}
								else
									strcpy_s(lpClientContext->SubjectLine,sizeof(lpClientContext->SubjectLine),HeaderValue);
								#ifdef TESTING_HEADER_LOGGING
								UpdateLogFile("SubjectLine","-",lpClientContext->SubjectLine);
								#endif
								TranslateAnnotatedChars(lpClientContext->SubjectLine);
							}
						}
						else if ((long) Position < (long) IoSize)
							HeaderSection = FALSE;
						if ((long) Position < (long) IoSize)
						{
							memset(HeaderItem,0,sizeof(HeaderItem));
							memset(HeaderValue,0,sizeof(HeaderValue));
						}
					}
				}
				else
				{
					FileFailure = TRUE;
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"ProcessFilter() Failed to read from file");
				}
			}
			fclose(lpClientContext->MessageFile);
			lpClientContext->FileOpen = FALSE;
		}
		else
		{
			Result = FALSE;
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"ProcessFilter() Failed to open file or file already open");
		}
	}
	if (Result && lpClientContext->MessageBody != NULL)
	{
		// remove extra space at end of message body that does not apply
		Length = strlen(lpClientContext->MessageBody);
		if (Length >= 3 && lpClientContext->MessageBody[Length-3] == '.' && lpClientContext->MessageBody[Length-2] == ' ' && lpClientContext->MessageBody[Length-1] == ' ')
		{
			lpClientContext->MessageBody[Length-3] = '\0';
			Length -= 3;
		}
		while (Length > 0 && lpClientContext->MessageBody[Length-1] == ' ' || lpClientContext->MessageBody[Length-1] == '\r' || lpClientContext->MessageBody[Length-1] == '\n' || lpClientContext->MessageBody[Length-1] == '\t')
		{
			lpClientContext->MessageBody[Length-1] = '\0';
			Length--;
		}
	}
	#ifdef TESTING_MESSAGE_LOGGING
	if (lpClientContext->MessageBody != NULL)
	{
		if (strlen(lpClientContext->MessageBody) == 0)
			UpdateLogFile(lpClientContext->AddressString,"Message","Blank");
		else
		{
			char TempString[1024];
			sprintf_s(TempString,sizeof(TempString),"strlen = %ld",strlen(lpClientContext->MessageBody));
			UpdateLogFile(lpClientContext->AddressString,TempString,lpClientContext->MessageBody);
		}
	}
	else
		UpdateLogFile(lpClientContext->AddressString,"Message","not Processed");
	#endif
	_time64(&lpClientContext->LastAccess);
	YieldControl();
	if (Result)// && ContinueProcess(lpClientContext,TRUE))
	{
		// Always perform this check
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = '4';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step 4",lpClientContext->FilteredBy);
		#endif
		CheckKeywordFilter(lpClientContext,lpClientContext->SubjectLine,TRUE,FALSE);
		CheckKeywordFilter(lpClientContext,lpClientContext->FromField,FALSE,TRUE);
	}
	if (Result)// && ContinueProcess(lpClientContext,TRUE))
	{
		// Always perform this check
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = '5';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step 5",lpClientContext->FilteredBy);
		#endif
		if (RemoveExtraSpace(lpClientContext,lpClientContext->SubjectLine,FALSE,IPWhiteList))
			CheckKeywordFilter(lpClientContext,lpClientContext->SubjectLine,TRUE,FALSE);
	}
	if (Result && ContinueProcess(lpClientContext,TRUE) && ReverseResolution && lpClientContext->BlackListType == BL_NONE && (!lpClientContext->WhiteList || (lpClientContext->WhiteList && lpClientContext->FilteredBy[0] != '[')) && strlen(lpClientContext->FromField) > 0)
	{
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = '6';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step 6",lpClientContext->FilteredBy);
		#endif
		ReverseResolveAddress(lpClientContext,lpClientContext->FromField);
	}
	if (Result && ContinueProcess(lpClientContext,FALSE))
	{
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = '7';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step 7",lpClientContext->FilteredBy);
		#endif
		for (Loop = 0; ContinueProcess(lpClientContext,FALSE) && Loop < DNSBLSourceCount && Loop < DNSBLResultsCount; Loop++)
			if (strlen(DNSBLSourcePtr[Loop]) > 0 && strlen(DNSBLResultsPtr[Loop]) > 0)
			{
				Num1 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[5];
				Num2 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[4];
				Num3 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[3];
				Num4 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[2];
				sprintf_s(Buffer,sizeof(Buffer),"%d.%d.%d.%d.%s",Num1,Num2,Num3,Num4,DNSBLSourcePtr[Loop]);
				#ifdef TESTING_DETAILED_LOGGING
				UpdateLogFile(lpClientContext->AddressString,"Performing DNSBL lookup of",Buffer);
				#endif
				if ((HostComputer = ::gethostbyname(Buffer)) != NULL)
				{
					if ((BYTE) (*(HostComputer->h_addr_list))[3] > 0 && (BYTE) (*(HostComputer->h_addr_list))[3] <= strlen(DNSBLResultsPtr[Loop]) && toupper(DNSBLResultsPtr[Loop][(BYTE) (*(HostComputer->h_addr_list))[3]-1]) == 'Y')
					{
						lpClientContext->BlackListType = BL_IP;
						lpClientContext->BlackListSubType = BL_SUB_IP_DNSBL;
						Num1 = (BYTE) (*(HostComputer->h_addr_list))[0];
						Num2 = (BYTE) (*(HostComputer->h_addr_list))[1];
						Num3 = (BYTE) (*(HostComputer->h_addr_list))[2];
						Num4 = (BYTE) (*(HostComputer->h_addr_list))[3];
						sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"DNSBL %s returned [%d.%d.%d.%d]",DNSBLSourcePtr[Loop],Num1,Num2,Num3,Num4);
						lpClientContext->BlackListResult = DNSBLAction;
						#ifdef TESTING_DETAILED_LOGGING
						UpdateLogFile(lpClientContext->AddressString,"-",lpClientContext->FilteredBy);
						#endif
					}
				}
				else
					UpdateLogFile(lpClientContext->AddressString,"Failed to receive data from",DNSBLSourcePtr[Loop]);
			}
	}
	if (Result && ContinueProcess(lpClientContext,FALSE) && !AcceptBlankBody)
	{
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = '8';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step 8",lpClientContext->FilteredBy);
		#endif
		if (!lpClientContext->EmptyMessage && !lpClientContext->MultiPartMessage && lpClientContext->MessageBody != NULL && lpClientContext->MessageSize < 750)
		{
			lpClientContext->EmptyMessage = TRUE;
			Position = strlen(lpClientContext->MessageBody);
			for (Loop = 0; lpClientContext->EmptyMessage && Loop < (int) Position; Loop++)
				if (lpClientContext->MessageBody[Loop] != ' ' && lpClientContext->MessageBody[Loop] != '.' && lpClientContext->MessageBody[Loop] != '\r' && lpClientContext->MessageBody[Loop] != '\n' && lpClientContext->MessageBody[Loop] != '\t')
					lpClientContext->EmptyMessage = FALSE;
		}

		// If message body is blank at this point then black list message
		if (!lpClientContext->WhiteList && !lpClientContext->PermBlackList && (lpClientContext->MessageBody == NULL || lpClientContext->EmptyMessage))
		{
			lpClientContext->BlackListType = BL_FORMAT;
			lpClientContext->BlackListSubType = BL_SUB_FORMAT_BODY;
			lpClientContext->BlackListResult = FormatErrors;
			sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"Blank Message Body");
		}
	}
	if (Result && ContinueProcess(lpClientContext,FALSE) && lpClientContext->MessageBody != NULL)
	{
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = '9';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step 9",lpClientContext->FilteredBy);
		#endif
		lpClientContext->ScanStep = 1;
		TranslateEncodedChars(lpClientContext,lpClientContext->MessageBody);

		#ifdef TESTING_MESSAGE_LOGGING
		if (lpClientContext->MessageBody != NULL)
		{
			char TempString[1024];
			sprintf_s(TempString,sizeof(TempString),"strlen = %ld",strlen(lpClientContext->MessageBody));
			UpdateLogFile(lpClientContext->AddressString,TempString,lpClientContext->MessageBody);
		}
		#endif
		RemoveHTMLLinkSpace(lpClientContext,lpClientContext->MessageBody);
		#ifdef TESTING_MESSAGE_LOGGING
		if (lpClientContext->MessageBody != NULL)
		{
			char TempString[1024];
			sprintf_s(TempString,sizeof(TempString),"strlen = %ld",strlen(lpClientContext->MessageBody));
			UpdateLogFile(lpClientContext->AddressString,TempString,lpClientContext->MessageBody);
		}
		#endif
		if (EncodingLimit > 0 && lpClientContext->CharReplacements > EncodingLimit && !lpClientContext->PermBlackList)
		{
			lpClientContext->WhiteList = FALSE;
			lpClientContext->BlackListType = BL_FORMAT;
			lpClientContext->BlackListSubType = BL_SUB_FORMAT_BODY;
			lpClientContext->BlackListResult = FormatErrors;
			sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"Found %d Encoded Characters",lpClientContext->CharReplacements);
		}
		#ifdef TESTING_DETAILED_LOGGING
		sprintf_s(Buffer,sizeof(Buffer),"Found %d Encoded chars",lpClientContext->CharReplacements);
		UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),Buffer);
		#endif
		CheckKeywordFilter(lpClientContext,lpClientContext->MessageBody,FALSE,FALSE);
	}
	if (Result && AlternateRouting > 0 && lpClientContext->MessageBody != NULL && (lpClientContext->WhiteList || lpClientContext->BlackListType == BL_NONE))
	{
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = 'X';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step X",lpClientContext->FilteredBy);
		#endif
		ExtractAddress(lpClientContext->FromField,HeaderItem,sizeof(HeaderItem),FALSE);
		if (_stricmp(HeaderItem,"rfq@fastquote.ilsmart.com") == 0 && lpClientContext->SubjectLine[0] == 'R' && lpClientContext->SubjectLine[1] == 'F' && lpClientContext->SubjectLine[2] == 'Q')
		{
//2003-Nov-06 13:29:14 Testing Subject RFQ Med-Air, Inc. Entry Code: 95HN-V547-QGDP
//2003-Nov-06 13:29:14 Testing rfq@fastquote.ilsmart.com RFQ Med-Air, Inc. Entry Code: 95HN-V547-QGDP
//2003-Nov-06 13:29:14 Testing strlen = 5005 To:   TURBO RESOURCES, INT'L Attn: Irv Hoffman  You have received a Request for Quote from:       Med-Air, Inc.       2450 N.W. 110th Avenue        Miami, FL 33172       United States       Email: mario@med-air.com       Phone: 1 305-592-6236       Fax:   1 305-592-8059  To reply via email, use your email program's "Reply To" button (be sure to include original text) and enter the information you wish to change in the brackets for each item.  No entry in the price field indicates a "No Quote".  RFQ Control Number: DIANAH 3 Quote by: 2:25PM Central Time (GMT -6 Hours), November 7, 2003 Traceability: Comments:  ITEM 1 Wanted        Part: 980-4100-DXUN        Description: RECORDER FLT DATA        Qty: 1 Cond: OH, SV         Your ILS listing shows the following item(s):        980-4100-DXUN          RECORDER         PLEASE QUOTE        Part Number*: [980-4100-DXUN]        Qty*: [1] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields  ITEM 2 Wanted        Part: 980-6109-017        Description: MONITOR        Qty: 1 Cond: OH, SV         Your ILS listing shows the following item(s):        980-6109-017           MONITOR         PLEASE QUOTE        Part Number*: [980-6109-017]        Qty*: [1] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields  ITEM 3 Wanted        Part: AW2835AH01        Description: INDICATOR        Qty: 1 Cond: OH, SV         Your ILS listing shows the following item(s):        AW2835AH01             INDICATR         PLEASE QUOTE        Part Number*: [AW2835AH01]        Qty*: [1] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields  ITEM 5 Wanted        Part: AYLF9732-1        Description: SENSOR        Qty: 1 Cond: OH, SV         Your ILS listing shows the following item(s):        AYLF-9732-1            SNSR         PLEASE QUOTE        Part Number*: [AYLF-9732-1]        Qty*: [1] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields  ITEM 7 Wanted        Part: G-5587        Description: PANEL        Qty: 1 Cond: OH, SV         Your ILS listing shows the following item(s):        G5587                  ATC         PLEASE QUOTE        Part Number*: [G5587]        Qty*: [1] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields  ITEM 8 Wanted        Part: G-6101        Description: PANEL        Qty: 1 Cond: OH, SV         Your ILS listing shows the following item(s):        G-6101                 CONTROL PANEL         PLEASE QUOTE        Part Number*: [G-6101]        Qty*: [1] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields  ITEM 9 Wanted        Part: LG80E1        Description: EPR TRAN        Qty: 1 Cond: OH, SV         Your ILS listing shows the following item(s):        LG80E1                 EPR         PLEASE QUOTE        Part Number*: [LG80E1]        Qty*: [1] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields  ITEM 11 Wanted        Part: RD-AX7010        Description: RPRD TAPE        Qty: 1 Cond: OH, SV         Your ILS listing shows the following item(s):        RD-AX7010              REPRODUCER AUDI
//2003-Nov-06 13:29:14 Testing strlen = 5005 O         PLEASE QUOTE        Part Number*: [RD-AX7010]        Qty*: [1] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields   To respond: 1. - Go to http://quote.ilsmart.com/    - Enter entry code: 95HN-V547-QGDP    or go directly to    - http://quote.ilsmart.com/FQ-Authenticate.asp?entrycode=95HN-V547-QGDP OR 2. via E-mail    - Reply to this message with original text    - Enter your quote information by replacing information within      the brackets         or    - No entry in the price fields indicates a "No Quote"  QUESTIONS? Contact ILS at cust.support@ilsmart.com  ILS is not responsible for delivery or contact.  View the disclaimer at http://www.ilsmart.com/disclaimer.htm.  When the link is selected, a new window should open that contains the disclaimer.  Powered by ILSmart.com   .  
//2003-Nov-06 13:29:14 206.175.69.66 White List [206.175.69.66]
//2003-Nov-06 13:29:19 Testing Subject RFQ Med-Air, Inc. Entry Code: B4PR-UKS7-Q1LL
//2003-Nov-06 13:29:19 Testing rfq@fastquote.ilsmart.com RFQ Med-Air, Inc. Entry Code: B4PR-UKS7-Q1LL
//2003-Nov-06 13:29:19 Testing strlen = 2208 To:   TURBO EXPENDABLES Attn: Sales  You have received a Request for Quote from:       Med-Air, Inc.       2450 N.W. 110th Avenue        Miami, FL 33172       United States       Email: mario@med-air.com       Phone: 1 305-592-6236       Fax:   1 305-592-8059  To reply via email, use your email program's "Reply To" button (be sure to include original text) and enter the information you wish to change in the brackets for each item.  No entry in the price field indicates a "No Quote".  RFQ Control Number: DIANAH 3 Quote by: 2:25PM Central Time (GMT -6 Hours), November 7, 2003 Traceability: Comments:  ITEM 9 Wanted        Part: LG80E1        Description: EPR TRAN        Qty: 1 Cond: OH, SV         Your ILS listing shows the following item(s):        LG80E1                 EPR         PLEASE QUOTE        Part Number*: [LG80E1]        Qty*: [1] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields  ITEM 11 Wanted        Part: RD-AX7010        Description: RPRD TAPE        Qty: 1 Cond: OH, SV         Your ILS listing shows the following item(s):        RD-AX7010              REPRODUCER AUDIO         PLEASE QUOTE        Part Number*: [RD-AX7010]        Qty*: [1] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields   To respond: 1. - Go to http://quote.ilsmart.com/    - Enter entry code: B4PR-UKS7-Q1LL    or go directly to    - http://quote.ilsmart.com/FQ-Authenticate.asp?entrycode=B4PR-UKS7-Q1LL OR 2. via E-mail    - Reply to this message with original text    - Enter your quote information by replacing information within      the brackets         or    - No entry in the price fields indicates a "No Quote"  QUESTIONS? Contact ILS at cust.support@ilsmart.com  ILS is not responsible for delivery or contact.  View the disclaimer at http://www.ilsmart.com/disclaimer.htm.  When the link is selected, a new window should open that contains the disclaimer.  Powered by ILSmart.com   .  
//2003-Nov-06 13:29:19 206.175.69.66 White List [206.175.69.66]
//2003-Nov-06 13:29:33 Testing Subject RFQ Paragon Int. Group Corp. Entry Code: MT8V-MHHV-UJ76
//2003-Nov-06 13:29:33 Testing rfq@fastquote.ilsmart.com RFQ Paragon Int. Group Corp. Entry Code: MT8V-MHHV-UJ76
//2003-Nov-06 13:29:33 Testing strlen = 1752 To:   TURBO EXPENDABLES Attn: Sales  You have received a Request for Quote from:       Paragon Int. Group Corp.       18800 Amar Rd.        Walnut, CA 91789       United States       Email: sales@paragon8.com       Phone: 1 626-965-5828       Fax:   1 626-965-5826  To reply via email, use your email program's "Reply To" button (be sure to include original text) and enter the information you wish to change in the brackets for each item.  No entry in the price field indicates a "No Quote".  RFQ Control Number: b3emu011439728 Quote by: 2:27PM Central Time (GMT -6 Hours), November 9, 2003 Traceability: Comments:  ITEM 1 Wanted        Part: nas6604-17        Description: BOLT        Qty: 50 Cond: NE, NS         Your ILS listing shows the following item(s):        NAS1304-17             BOLT         PLEASE QUOTE        Part Number*: [NAS1304-17]        Qty*: [50] Cond*: [ ] AR, NE, NS, OH, SV        Price US$: [ ] (no entry indicates "No Quote")        Traceability: [ ]        Lead-time from date of purchase: [ ] days        Comments: [    ]        *Required Fields   To respond: 1. - Go to http://quote.ilsmart.com/    - Enter entry code: MT8V-MHHV-UJ76    or go directly to    - http://quote.ilsmart.com/FQ-Authenticate.asp?entrycode=MT8V-MHHV-UJ76 OR 2. via E-mail    - Reply to this message with original text    - Enter your quote information by replacing information within      the brackets         or    - No entry in the price fields indicates a "No Quote"  QUESTIONS? Contact ILS at cust.support@ilsmart.com  ILS is not responsible for delivery or contact.  View the disclaimer at http://www.ilsmart.com/disclaimer.htm.  When the link is selected, a new window should open that contains the disclaimer.  Powered by ILSmart.com   .  
//2003-Nov-06 13:29:33 206.175.69.66 White List [206.175.69.66]
		}
		else if (FALSE)
		{
			lpClientContext->MessageIdentified = TRUE;
			char TempString[1024];
			sprintf_s(TempString,sizeof(TempString),"strlen = %ld",strlen(lpClientContext->MessageBody));
			UpdateLogFile(lpClientContext->AddressString,TempString,lpClientContext->MessageBody);
		}
	}
	if (Result && ContinueProcess(lpClientContext,FALSE) && lpClientContext->MessageBody != NULL && strlen(lpClientContext->MessageBody) > 0)
	{
		#ifdef TESTING_MESSAGE_LOGGING
		if (lpClientContext->MessageBody != NULL)
		{
			char TempString[1024];
			sprintf_s(TempString,sizeof(TempString),"strlen = %ld",strlen(lpClientContext->MessageBody));
			UpdateLogFile(lpClientContext->AddressString,TempString,lpClientContext->MessageBody);
		}
		#endif
		lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = 'A';
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing step A",lpClientContext->FilteredBy);
		#endif
		lpClientContext->ScanStep = 2;
		if (RemoveExtraSpace(lpClientContext,lpClientContext->MessageBody,TRUE,IPWhiteList))
			if (ContinueProcess(lpClientContext,FALSE))
			{
				// This is called a second time to make sure extra spaces between the HTML tags is cleared up
				RemoveExtraSpace(lpClientContext,lpClientContext->MessageBody,TRUE,IPWhiteList);
				CheckKeywordFilter(lpClientContext,lpClientContext->MessageBody,FALSE,FALSE);
			}
		#ifdef TESTING_MESSAGE_LOGGING
		if (lpClientContext->MessageBody != NULL)
		{
			char TempString[1024];
			sprintf_s(TempString,sizeof(TempString),"strlen = %ld",strlen(lpClientContext->MessageBody));
			UpdateLogFile(lpClientContext->AddressString,TempString,lpClientContext->MessageBody);
		}
		#endif
	}
	else if (Result && lpClientContext->MessageBody != NULL && strlen(lpClientContext->MessageBody) > 0)
	{
		if (!lpClientContext->PermBlackList && (!lpClientContext->WhiteList || !IPWhiteList))
		{
			lpClientContext->StepsTaken[strlen(lpClientContext->StepsTaken)] = 'B';
			#ifdef TESTING_DETAILED_LOGGING
			UpdateLogFile(lpClientContext->AddressString,"Performing step B",lpClientContext->FilteredBy);
			#endif
			lpClientContext->ScanStep = 2;
			#ifdef TESTING_MESSAGE_LOGGING
			if (lpClientContext->MessageBody != NULL)
			{
				char TempString[1024];
				sprintf_s(TempString,sizeof(TempString),"strlen = %ld",strlen(lpClientContext->MessageBody));
				UpdateLogFile(lpClientContext->AddressString,TempString,lpClientContext->MessageBody);
			}
			#endif
			TranslateEncodedChars(lpClientContext,lpClientContext->MessageBody);
			RemoveHTMLLinkSpace(lpClientContext,lpClientContext->MessageBody);
			#ifdef TESTING_MESSAGE_LOGGING
			if (lpClientContext->MessageBody != NULL)
			{
				char TempString[1024];
				sprintf_s(TempString,sizeof(TempString),"strlen = %ld",strlen(lpClientContext->MessageBody));
				UpdateLogFile(lpClientContext->AddressString,TempString,lpClientContext->MessageBody);
			}
			#endif
			RemoveExtraSpace(lpClientContext,lpClientContext->MessageBody,TRUE,IPWhiteList);
			if (ForwardResolution && (!lpClientContext->WhiteList || !IPWhiteList) && !lpClientContext->PermBlackList && (lpClientContext->WhiteList || lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListResult == BL_RESULT_FORWARD))
				if (lpClientContext->MessageBody != NULL)
				{
					#ifdef TESTING_MESSAGE_LOGGING
					char TempString[1024];

					sprintf_s(TempString,sizeof(TempString),"ForwardResolution=%d,lpClientContext->WhiteList=%d,IPWhiteList=%d,lpClientContext->PermBlackList=%d,lpClientContext->BlackListType=%d,lpClientContext->BlackListResult=%d",ForwardResolution,lpClientContext->WhiteList,IPWhiteList,lpClientContext->PermBlackList,lpClientContext->BlackListType,lpClientContext->BlackListResult);
					UpdateLogFile(lpClientContext->AddressString,"Step F:",TempString);
					sprintf_s(TempString,sizeof(TempString),"strlen=%ld, links=%d, Steps='%s'",strlen(lpClientContext->MessageBody),lpClientContext->HTMLLinks,lpClientContext->StepsTaken);
					UpdateLogFile(lpClientContext->AddressString,"Step F:",TempString);
					#endif
					RemoveExtraSpace(lpClientContext,lpClientContext->MessageBody,TRUE,IPWhiteList);
					#ifdef TESTING_MESSAGE_LOGGING
					sprintf_s(TempString,sizeof(TempString),"ForwardResolution=%d,lpClientContext->WhiteList=%d,IPWhiteList=%d,lpClientContext->PermBlackList=%d,lpClientContext->BlackListType=%d,lpClientContext->BlackListResult=%d",ForwardResolution,lpClientContext->WhiteList,IPWhiteList,lpClientContext->PermBlackList,lpClientContext->BlackListType,lpClientContext->BlackListResult);
					UpdateLogFile(lpClientContext->AddressString,"Step F:",TempString);
					sprintf_s(TempString,sizeof(TempString),"Step F: strlen=%ld, links=%d,",strlen(lpClientContext->MessageBody),lpClientContext->HTMLLinks);
					UpdateLogFile(lpClientContext->AddressString,TempString,lpClientContext->MessageBody);
					#endif
				}
		}
	}
	#ifdef TESTING_DETAILED_LOGGING
	UpdateLogFile(lpClientContext->AddressString,"ProcessFilter() complete",lpClientContext->FilteredBy);
	#endif
	lpClientContext->ScanStep = 3;

	if (!lpClientContext->FileOpen && (lpClientContext->MessageTruncated || lpClientContext->MessageIncomplete))
	{
		// Add a message on the e-mail to indicate it's been truncated or incomplete
		if (fopen_s(&lpClientContext->MessageFile,lpClientContext->FullFileName,"ab") == 0)
		{
			lpClientContext->FileOpen = TRUE;
			if (!lpClientContext->MultiPartMessage || lpClientContext->CurrentBoundary < 0)
			{
				if (lpClientContext->MessageTruncated)
				{
					if (lpClientContext->FileOpen)
						if (fprintf(lpClientContext->MessageFile,"\r\n\r\nThis message has been truncated due to size...\r\n.\r\n") < 0)
							lpClientContext->FileOpen = FALSE;
				}
				else
				{
					if (lpClientContext->FileOpen)
						if (fprintf(lpClientContext->MessageFile,"\r\n\r\nThis message may be incomplete...\r\n.\r\n") < 0)
							lpClientContext->FileOpen = FALSE;
				}
			}
			else
			{
				// If the final message boundary is found then assume the message was not properly formatted with
				// the end-of-message marker.  Otherwise, append a message indicating it's truncated or incomplete.
				if (!lpClientContext->MessageTruncated && lpClientContext->MessageIncomplete && lpClientContext->EndOfMessageBoundary && lpClientContext->CurrentBoundary == 0)
				{
					lpClientContext->MessageIncomplete = FALSE;
					if (lpClientContext->FileOpen)
						if (fprintf(lpClientContext->MessageFile,"\r\n.\r\n") < 0)
							lpClientContext->FileOpen = FALSE;
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Message missing End-of-message Marker");
				}
				else
				{
					while (lpClientContext->CurrentBoundary > 0)
					{
						if (lpClientContext->FileOpen)
							if (fprintf(lpClientContext->MessageFile,"\r\n\r\n%s--",lpClientContext->Boundary[lpClientContext->CurrentBoundary]) < 0)
								lpClientContext->FileOpen = FALSE;
						lpClientContext->CurrentBoundary--;
					}
					if (lpClientContext->FileOpen)
						if (fprintf(lpClientContext->MessageFile,"\r\n\r\n%s\r\n",lpClientContext->Boundary[lpClientContext->CurrentBoundary]) < 0)
							lpClientContext->FileOpen = FALSE;
					if (lpClientContext->MessageTruncated)
					{
						if (lpClientContext->FileOpen)
						{
							if (fprintf(lpClientContext->MessageFile,"%s","Content-Type: application/octet-stream; name=\"Truncated.txt\"\r\nContent-Transfer-Encoding: BASE64\r\n\r\n") < 0)
								lpClientContext->FileOpen = FALSE;
							else if (fprintf(lpClientContext->MessageFile,"%s","VGhpcyBtZXNzYWdlIGhhcyBiZWVuIHRydW5jYXRlZCBkdWUgdG8gc2l6ZS4uLgAA==") < 0)
								lpClientContext->FileOpen = FALSE;
						}
					}
					else
					{
						if (lpClientContext->FileOpen)
						{
							if (fprintf(lpClientContext->MessageFile,"%s","Content-Type: application/octet-stream; name=\"Incomplete.txt\"\r\nContent-Transfer-Encoding: BASE64\r\n\r\n") < 0)
								lpClientContext->FileOpen = FALSE;
							else if (fprintf(lpClientContext->MessageFile,"%s","VGhpcyBtZXNzYWdlIG1heSBiZSBpbmNvbXBsZXRlLi4u") < 0)
								lpClientContext->FileOpen = FALSE;
						}
					}
					if (lpClientContext->FileOpen)
						if (fprintf(lpClientContext->MessageFile,"\r\n\r\n%s--\r\n.\r\n",lpClientContext->Boundary[lpClientContext->CurrentBoundary]) < 0)
							lpClientContext->FileOpen = FALSE;
				}
			}
			fclose(lpClientContext->MessageFile);
			lpClientContext->FileOpen = FALSE;
		}
	}
	_time64(&lpClientContext->LastAccess);
	YieldControl();
	if (FileFailure && !lpClientContext->WhiteList && lpClientContext->BlackListType == BL_NONE)
		Result = FALSE;
	return(Result);
}

int ExtractHeaderElement(char *Source,int SourceSize,char *Item,int MaxItemSize,char *Value,int MaxValueSize,BOOL *AllSpaces)
{
	int		MoveCount = 0,LookAhead,HeaderPosition,ItemPosition = 0,NewPosition;

	*AllSpaces = TRUE;
	if (strlen(Source) > 0)
	{
		if (MoveCount+2 < SourceSize && Source[MoveCount] == '\r' && Source[MoveCount+1] == '\r' && Source[MoveCount+2] == '\n')
			MoveCount += 3;
		else if (MoveCount+1 < SourceSize && Source[MoveCount] == '\r' && Source[MoveCount+1] == '\n')
			MoveCount += 2;
		else if (MoveCount < SourceSize && Source[MoveCount] == '\r')
			MoveCount++;
		else if (MoveCount < SourceSize && Source[MoveCount] == '\n')
			MoveCount++;
		while (MoveCount < SourceSize && (int) strlen(Value) < MaxValueSize-1 && Source[MoveCount] != '\r' && Source[MoveCount] != '\n')
		{
			if (Source[MoveCount] == '\t')
				Value[strlen(Value)] = ' ';
			else
				Value[strlen(Value)] = Source[MoveCount];
			if (Value[strlen(Value)-1] != ' ')
				*AllSpaces = FALSE;
			MoveCount++;

			// Check if next line is tabbed in, if so then it's a continuation of current line
			if (MoveCount < SourceSize && (int) strlen(Value) < MaxValueSize-1 && (Source[MoveCount] == '\r' || Source[MoveCount] == '\n'))
			{
				LookAhead = MoveCount;
				if (LookAhead+2 < SourceSize && Source[LookAhead] == '\r' && Source[LookAhead+1] == '\r' && Source[LookAhead+2] == '\n')
					LookAhead += 3;
				else if (LookAhead+1 < SourceSize && Source[LookAhead] == '\r' && Source[LookAhead+1] == '\n')
					LookAhead += 2;
				else if (LookAhead < SourceSize && Source[LookAhead] == '\r')
					LookAhead++;
				else if (LookAhead < SourceSize && Source[LookAhead] == '\n')
					LookAhead++;
				if (Source[LookAhead] == ' ' || Source[LookAhead] == '\t')
					MoveCount = LookAhead;
			}
		}
		if (MoveCount < SourceSize)
		{
			// Split header element and remove any leading or trailing spaces
			while (strlen(Value) > 0 && Value[strlen(Value)-1] == ' ')
				Value[strlen(Value)-1] = '\0';
			HeaderPosition = 0;
			while (HeaderPosition < (int) strlen(Value) && (Value[HeaderPosition] == ' ' || Value[HeaderPosition] == '\t'))
				HeaderPosition++;
			while (HeaderPosition < (int) strlen(Value) && Value[HeaderPosition] != ':' && ItemPosition < MaxItemSize-1)
			{
				Item[ItemPosition] = Value[HeaderPosition];
				ItemPosition++;
				HeaderPosition++;
			}
			if (HeaderPosition < (int) strlen(Value) && Value[HeaderPosition] == ':')
				HeaderPosition++;
			while (HeaderPosition < (int) strlen(Value) && Value[HeaderPosition] == ' ')
				HeaderPosition++;
			NewPosition = 0;
			while (HeaderPosition <= (int) strlen(Value))
			{
				Value[NewPosition] = Value[HeaderPosition];
				HeaderPosition++;
				NewPosition++;
			}
		}
	}
	Item[ItemPosition] = '\0';
	TranslateString(Value);
	#ifdef TESTING_HEADER_LOGGING
	UpdateLogFile("ExtractHeaderElement()",Item,Value);
	#endif
	return(MoveCount);
}

int ExtractBodyLine(char *Source,int SourceSize,char *BodyLine,int MaxSize,BOOL *AllSpaces)
{
	int		MoveCount = 0;

	*AllSpaces = TRUE;
	if (strlen(Source) > 0)
	{
		if (MoveCount+1 < SourceSize && Source[MoveCount] == '\r' && Source[MoveCount+1] == '\n')
			MoveCount += 2;
		else if (MoveCount < SourceSize && Source[MoveCount] == '\r')
			MoveCount++;
		else if (MoveCount < SourceSize && Source[MoveCount] == '\n')
			MoveCount++;
		while (MoveCount < SourceSize && (int) strlen(BodyLine) < MaxSize-1 && Source[MoveCount] != '\r' && Source[MoveCount] != '\n')
		{
			BodyLine[strlen(BodyLine)] = Source[MoveCount];
			if (BodyLine[strlen(BodyLine)-1] != ' ')
				*AllSpaces = FALSE;
			MoveCount++;
		}
	}
	#ifdef TESTING_MESSAGE_LINE_LOGGING
	UpdateLogFile("ExtractBodyLine()","-",BodyLine);
	#endif
	return(MoveCount);
}

void TranslateString(char *Source)
{
	char	Buffer[MAX_MESSAGE_BUFFER],CharSet[MAX_MESSAGE_BUFFER],CodeBuffer[MAX_MESSAGE_BUFFER];
	int		SourcePosition = 0,BufferPosition = 0,CharSetPosition = 0,CodeBufferPosition,Position;
	BOOL	FoundCoding,FoundCharSet;

//From: =?koi8-r?B?/NTPINDPzc/WxdQg?= <van1972siri@zdi.com>
//Subject: =?koi8-r?B?78TJziDExc7YINDPyM/WIM7BIMTS1cfPyj8g8M/SwSDe1M8t1M8g0A==?=
//		=?koi8-r?B?z83FztHU2CE=?=
	memset(Buffer,0,sizeof(Buffer));
	memset(CharSet,0,sizeof(CharSet));
	while (Source[SourcePosition] != '\0' && BufferPosition < sizeof(Buffer)-1)
	{
		if (Source[SourcePosition] != '=' || Source[SourcePosition+1] != '?')
			Buffer[BufferPosition] = Source[SourcePosition];
		else
		{
			memset(CodeBuffer,0,sizeof(CodeBuffer));
			FoundCoding = FALSE;
			FoundCharSet = FALSE;
			Position = SourcePosition+2;
			while (Source[Position] != '?' && Source[Position] != '\0')
			{
				if (!FoundCharSet)
				{
					CharSet[CharSetPosition] = ' ';
					CharSetPosition++;
				}
				FoundCharSet = TRUE;
				CharSet[CharSetPosition] = Source[Position];
				Position++;
				CharSetPosition++;
			}
			if (Source[Position] == '?' && (Source[Position+1] == 'B' || Source[Position+1] == 'b') && Source[Position+2] == '?')
			{
				// Found MIME encoding
				FoundCoding = TRUE;
				CodeBufferPosition = 0;
				Position += 3;
				while (CodeBufferPosition < sizeof(CodeBuffer)-1 && Source[Position] != ' ' && Source[Position] != '\t' && Source[Position] != '\r' && Source[Position] != '\n' && Source[Position] != '\0' && (Source[Position] != '?' || Source[Position+1] != '='))
				{
					CodeBuffer[CodeBufferPosition] = Source[Position];
					CodeBufferPosition++;
					Position++;
				}
				if (Source[Position] == '?' && Source[Position+1] == '=')
				{
					CodeBuffer[CodeBufferPosition] = Source[Position];
					CodeBufferPosition++;
					Position++;
					CodeBuffer[CodeBufferPosition] = Source[Position];
					CodeBufferPosition++;
					Position++;
				}
				MimeDecodeLine(CodeBuffer,64);
			}
			else if (Source[Position] == '?' && (Source[Position+1] == 'Q' || Source[Position+1] == 'q') && Source[Position+2] == '?')
			{
				// Found hex encoding
				FoundCoding = TRUE;
				CodeBufferPosition = 0;
				Position += 3;
				while (CodeBufferPosition < sizeof(CodeBuffer)-1 && Source[Position] != ' ' && Source[Position] != '\t' && Source[Position] != '\r' && Source[Position] != '\n' && Source[Position] != '\0' && (Source[Position] != '?' || Source[Position+1] != '='))
				{
					CodeBuffer[CodeBufferPosition] = Source[Position];
					CodeBufferPosition++;
					Position++;
				}
				if (Source[Position] == '?' && Source[Position+1] == '=')
					Position += 2;
				HexDecodeLine(CodeBuffer);
			}
			if (FoundCoding)
			{
				if (BufferPosition+strlen(CodeBuffer) < sizeof(Buffer)-1)
				{
					strcat_s(Buffer,sizeof(Buffer),CodeBuffer);
					BufferPosition = strlen(Buffer)-1;
				}
				SourcePosition = Position-1;
			}
			else
				Buffer[BufferPosition] = Source[SourcePosition];
		}
		SourcePosition++;
		BufferPosition++;
	}
	if (strlen(CharSet) > 0)
		strcat_s(Buffer,sizeof(Buffer),CharSet);
	strcpy_s(Source,MAX_MESSAGE_BUFFER,Buffer);
}

void MimeDecodePrepare()
{
	int		Loop;
	char	cTemp;

	for (Loop = 0, cTemp = 'A'; cTemp <= 'Z'; Loop++, cTemp++)
		MimecLookup64[Loop] = cTemp;
	for (Loop = 26, cTemp = 'a'; cTemp <= 'z'; Loop++, cTemp++)
		MimecLookup64[Loop] = cTemp;
	for (Loop = 52, cTemp = '0'; cTemp <= '9'; Loop++, cTemp++)
		MimecLookup64[Loop] = cTemp;
	MimecLookup64[62] = '+';
	MimecLookup64[63] = '/';

	for (Loop = 0, cTemp = 'A'; cTemp <= 'Z'; Loop++, cTemp++)
		MimecLookup32[Loop] = cTemp;
	for (Loop = 26, cTemp = '2'; cTemp <= '7'; Loop++, cTemp++)
		MimecLookup32[Loop] = cTemp;

	for (Loop = 0, cTemp = '0'; cTemp <= '9'; Loop++, cTemp++)
		MimecLookup16[Loop] = cTemp;
	for (Loop = 10, cTemp = 'A'; cTemp <= 'F'; Loop++, cTemp++)
		MimecLookup16[Loop] = cTemp;
}

void MimeDecodeLine(char *Source,int Base)
{
	int				Loop,Loop2,Position,WritePosition,SourceLen;
	BYTE			cByteIn[8];
	char			cBlock[6];
	BOOL			FoundItem;

	if (Base == 64)
	{
		// Base64 and 6bit
		Position = 0;
		WritePosition = 0;
		SourceLen = (int) strlen(Source);
		while (Position <= SourceLen-4)
		{
			for (Loop = 0; Loop < 4; Loop++)
				cByteIn[Loop] = Source[Position+Loop];
			Position += 4;
			for (Loop = 0; Loop < 4; Loop ++)
			{
				FoundItem = FALSE;
				for (Loop2 = 0; !FoundItem && Loop2 < 64; Loop2++)
					if (MimecLookup64[Loop2] == cByteIn[Loop])
					{
						cByteIn[Loop] = Loop2;
						FoundItem = TRUE;
					}
				if (!FoundItem && cByteIn[Loop] == '-')
				{
					cByteIn[Loop] = 62;
					FoundItem = TRUE;
				}
				if (!FoundItem && cByteIn[Loop] == '_')
				{
					cByteIn[Loop] = 63;
					FoundItem = TRUE;
				}
				if (!FoundItem)
					cByteIn[Loop] = '\0';
			}
			cBlock[0] = (cByteIn[0] << 2) + (cByteIn[1] >> 4);
			cBlock[1] = (cByteIn[1] << 4) + (cByteIn[2] >> 2);
			cBlock[2] = (cByteIn[2] << 6) + cByteIn[3];
			cBlock[3] = '\0';
			strcpy_s(&Source[WritePosition],sizeof(cBlock),cBlock);
			WritePosition += 3;
		}
	}
	if (Base == 32)
	{
		// Base32 and 5bit
		Position = 0;
		WritePosition = 0;
		SourceLen = (int) strlen(Source);
		while (Position <= SourceLen-8)
		{
			for (Loop = 0; Loop < 8; Loop++)
				cByteIn[Loop] = Source[Position+Loop];
			Position += 8;
			for (Loop = 0; Loop < 8; Loop ++)
			{
				FoundItem = FALSE;
				for (Loop2 = 0; !FoundItem && Loop2 < 32; Loop2++)
					if (MimecLookup32[Loop2] == toupper(cByteIn[Loop]))
					{
						cByteIn[Loop] = Loop2;
						FoundItem = TRUE;
					}
				if (!FoundItem)
					cByteIn[Loop] = '\0';
			}
			cBlock[0] = (cByteIn[0] << 3) + (cByteIn[1] >> 2);
			cBlock[1] = (cByteIn[1] << 6) + (cByteIn[2] << 1) + (cByteIn[3] >> 4);
			cBlock[2] = (cByteIn[3] << 4) + (cByteIn[4] >> 1);
			cBlock[3] = (cByteIn[4] << 7) + (cByteIn[5] << 2) + (cByteIn[6] >> 3);
			cBlock[4] = (cByteIn[6] << 5) + cByteIn[7];
			cBlock[5] = '\0';
			strcpy_s(&Source[WritePosition],sizeof(cBlock),cBlock);
			WritePosition += 5;
		}
	}
	if (Base == 16)
	{
		// Base16, 4bit and Hex
		Position = 0;
		WritePosition = 0;
		SourceLen = (int) strlen(Source);
		while (Position <= SourceLen-2)
		{
			for (Loop = 0; Loop < 2; Loop++)
				cByteIn[Loop] = Source[Position+Loop];
			Position += 2;
			for (Loop = 0; Loop < 2; Loop ++)
			{
				FoundItem = FALSE;
				for (Loop2 = 0; !FoundItem && Loop2 < 16; Loop2++)
					if (MimecLookup16[Loop2] == toupper(cByteIn[Loop]))
					{
						cByteIn[Loop] = Loop2;
						FoundItem = TRUE;
					}
				if (!FoundItem)
					cByteIn[Loop] = '\0';
			}
			cBlock[0] = (cByteIn[0] << 4) + cByteIn[1];
			cBlock[1] = '\0';
			strcpy_s(&Source[WritePosition],sizeof(cBlock),cBlock);
			WritePosition += 1;
		}
	}
}

void HexDecodeLine(char *Source)
{
	int		Loop;
	char	CodeString[10],CodeValue[2];

	for (Loop = 0; Loop < 256; Loop++)
		if (Loop != 61)
		{
			if (Loop < 16)
				sprintf_s(CodeString,sizeof(CodeString),"=0%X",Loop);
			else
				sprintf_s(CodeString,sizeof(CodeString),"=%X",Loop);
			CodeValue[0] = Loop;
			CodeValue[1] = '\0';
			if (Loop < 32)
				CodeValue[0] = ' ';
			SearchAndReplace(Source,CodeString,CodeValue,NULL);
		}
	SearchAndReplace(Source,"=3D","=",NULL);
}

void TranslateEncodedChars(CLIENT_CONTEXT *lpClientContext,char *Source)
{
	char	CodeString[15],CodeValue[2];
	int		Loop;
	BOOL	CountReplacement = FALSE;

	if (strlen(Source) > 0)
	{
		for (Loop = 0; Loop < 256; Loop++)
			if (Loop != 37)
			{
				CountReplacement = FALSE;
				if ((Loop >= 'a' && Loop <= 'z') || (Loop >= 'A' && Loop <= 'Z') || (Loop >= '0' && Loop <= '9') || Loop == '.')
					CountReplacement = TRUE;
				CodeValue[0] = Loop;
				CodeValue[1] = '\0';
				if (Loop < 32)
					CodeValue[0] = ' ';
				if (Loop < 16)
					sprintf_s(CodeString,sizeof(CodeString),"%%0%X",Loop);
				else
					sprintf_s(CodeString,sizeof(CodeString),"%%%X",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
			}
		SearchAndReplace(lpClientContext->MessageBody,"%25","%",NULL);

		for (Loop = 0; Loop < 256; Loop++)
			if (Loop != 38)
			{
				CountReplacement = FALSE;
				if ((Loop >= 'a' && Loop <= 'z') || (Loop >= 'A' && Loop <= 'Z') || (Loop >= '0' && Loop <= '9') || Loop == '.')
					CountReplacement = TRUE;
				CodeValue[0] = Loop;
				CodeValue[1] = '\0';
				if (Loop < 32)
					CodeValue[0] = ' ';
				sprintf_s(CodeString,sizeof(CodeString),"&#%d;",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
				if (Loop < 10)
				{
					sprintf_s(CodeString,sizeof(CodeString),"&#%02d;",Loop);
					SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
					sprintf_s(CodeString,sizeof(CodeString),"&#%02d;",Loop);
					SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
				}
				if (Loop < 100)
				{
					sprintf_s(CodeString,sizeof(CodeString),"&#%03d;",Loop);
					SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
				}
				sprintf_s(CodeString,sizeof(CodeString),"&#%04d;",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
				sprintf_s(CodeString,sizeof(CodeString),"&#%05d;",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
				sprintf_s(CodeString,sizeof(CodeString),"&#%06d;",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
				sprintf_s(CodeString,sizeof(CodeString),"&#x%X;",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
				sprintf_s(CodeString,sizeof(CodeString),"&#x0%X;",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
				sprintf_s(CodeString,sizeof(CodeString),"&#x00%X;",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
				sprintf_s(CodeString,sizeof(CodeString),"&#x000%X;",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
				sprintf_s(CodeString,sizeof(CodeString),"&#x0000%X;",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
			}
		SearchAndReplace(lpClientContext->MessageBody,"&#8211;","-",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&#8212;","-",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&ndash;","-",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&mdash;","-",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&#8216;","'",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&#8217;","'",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&lsquo;","'",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&rsquo;","'",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&#8220;","\"",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&#8221;","\"",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&#733;","\"",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&ldquo;","\"",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&rdquo;","\"",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&dblac;","\"",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&#732;","~",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&tilde;","~",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&nbsp;"," ",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&quot;","\"",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&lt;","<",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&gt;",">",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&amp;","&",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&#38;","&",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&acirc;","a",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&ecirc;","e",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&icirc;","i",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&ocirc;","o",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&ucirc;","u",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&aacute;","a",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&eacute;","e",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&iacute;","i",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&oacute;","o",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&uacute;","u",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&yacute;","y",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&agrave;","a",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&egrave;","e",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&igrave;","i",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&ograve;","o",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&ugrave;","u",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&auml;","a",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&euml;","e",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&iuml;","i",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&ouml;","o",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&uuml;","u",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&yuml;","y",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&atilde;","a",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&otilde;","o",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&ntilde;","n",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&oslash;","o",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"&aring;","a",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"Ê","ae",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"∆","ae",NULL);
		SearchAndReplace(lpClientContext->MessageBody,"\t"," ",NULL);
		TranslateAnnotatedChars(lpClientContext->MessageBody);

		// One more time for double encoding
		for (Loop = 0; Loop < 256; Loop++)
			if (Loop != 37)
			{
				CountReplacement = FALSE;
				if ((Loop >= 'a' && Loop <= 'z') || (Loop >= 'A' && Loop <= 'Z') || (Loop >= '0' && Loop <= '9') || Loop == '.')
					CountReplacement = TRUE;
				CodeValue[0] = Loop;
				CodeValue[1] = '\0';
				if (Loop < 32)
					CodeValue[0] = ' ';
				if (Loop < 16)
					sprintf_s(CodeString,sizeof(CodeString),"%%0%X",Loop);
				else
					sprintf_s(CodeString,sizeof(CodeString),"%%%X",Loop);
				SearchAndReplace(lpClientContext->MessageBody,CodeString,CodeValue,(CountReplacement ? &lpClientContext->CharReplacements : NULL));
			}
		SearchAndReplace(lpClientContext->MessageBody,"%25","%",NULL);
	}
}

void TranslateAnnotatedChars(char *Source)
{
	int		Loop,Loop2;
	BOOL	CharFound;
	char	AnnotatedChars[120],RealChars[120];

	strcpy_s(AnnotatedChars,sizeof(AnnotatedChars),"`¥íëîì\t\r\nÂ„‚·‡‰≈ƒ√¬¡¿ÍÈËÎÀ…» ÓÌÏÔ°œŒÃÕÙÛÚˆı¯÷“”‘’ÿ§˚˙˘¸‹Ÿ⁄€µÒ—˝ˇ›•óòÁ«¢ﬂ–ø˛ﬁ£ß∂©Æ®±◊˜´ª∞∫π≤≥∑™¨≠Ø∏ºΩæ¶|");
	strcpy_s(RealChars,sizeof(RealChars),"''''\"\"   aaaaaaaaaaaaeeeeeeeeiiiiiiiiioooooooooooooouuuuuuuuunnyyyy-~cccbd?ppfspcr +x-<>o0123         ii");
	for (Loop = strlen(Source)-1; Loop >= 0; Loop--)
	{
		CharFound = FALSE;
		for (Loop2 = strlen(AnnotatedChars)-1; !CharFound && Loop2 >= 0; Loop2--)
			if (Source[Loop] == AnnotatedChars[Loop2])
			{
				Source[Loop] = RealChars[Loop2];
				CharFound = TRUE;
			}
	}
}

void ExtractAddress(char *MailAddress,char *Storage,int MaxStorageSize,BOOL MailFromAddress)
{
	int		Position,DestPosition = 0,LastBracketPosition = -1;
	BOOL	FoundBrackets = FALSE,InsideBrackets = FALSE,AllSpaces = TRUE,ExtractedAddress = FALSE;

	memset(Storage,0,MaxStorageSize);
	for (Position = 0; Position < (int) strlen(MailAddress); Position++)
	{
		if (InsideBrackets && MailAddress[Position] == '>')
		{
			InsideBrackets = FALSE;
			ExtractedAddress = TRUE;
			LastBracketPosition = Position;
		}
		else if (InsideBrackets)
		{
			Storage[DestPosition] = MailAddress[Position];
			if (Storage[DestPosition] != ' ' && Storage[DestPosition] != '\r' && Storage[DestPosition] != '\n' && Storage[DestPosition] != '\t')
				AllSpaces = FALSE;
			DestPosition++;
		}
		else if (MailAddress[Position] == '<' && !ExtractedAddress)
		{
			FoundBrackets = TRUE;
			InsideBrackets = TRUE;
		}
	}
	if (InsideBrackets && DestPosition > 0)
	{
		InsideBrackets = FALSE;
		ExtractedAddress = TRUE;
		LastBracketPosition = Position-1;
	}
	if (LastBracketPosition < 0)
		FoundBrackets = FALSE;
	if (!FoundBrackets && (int) strlen(MailAddress) < MaxStorageSize)
		strcpy_s(Storage,MaxStorageSize,MailAddress);

	// If address is blank but more characters follow the brackets then assume the address is after the brackets
	if (AllSpaces && FoundBrackets && LastBracketPosition+1 < (int) strlen(MailAddress)-1 && (int) strlen(MailAddress)-LastBracketPosition < MaxStorageSize)
		strcpy_s(Storage,MaxStorageSize,&MailAddress[LastBracketPosition+1]);

	// Remove any leading or trailing spaces and other non-visible characters
	DestPosition = strlen(Storage)-1;
	while (DestPosition > 0 && (Storage[DestPosition] == ' ' || Storage[DestPosition] == '\r' || Storage[DestPosition] == '\n' || Storage[DestPosition] == '\t'))
	{
		Storage[DestPosition] = '\0';
		DestPosition--;
	}
	DestPosition = 0;
	while (DestPosition < (int) strlen(Storage) && (Storage[DestPosition] == ' ' || Storage[DestPosition] == '\r' || Storage[DestPosition] == '\n' || Storage[DestPosition] == '\t'))
		DestPosition++;
	if (DestPosition > 0 && DestPosition < (int) strlen(Storage))
	{
		Position = DestPosition;
		DestPosition = 0;
		while (Storage[Position] != '\0')
		{
			Storage[DestPosition] = Storage[Position];
			Position++;
			DestPosition++;
		}
		Storage[DestPosition] = '\0';
	}

	// Break at a space if address contains one
	DestPosition = 0;
	while (DestPosition < (int) strlen(Storage))
	{
		if (Storage[DestPosition] == ' ')
			Storage[DestPosition] = '\0';
		DestPosition++;
	}

	// Check for blank Mail From address
	if (MailFromAddress && AcceptBlankMailFrom && !ValidAddress(Storage) && (FindString(MailAddress,"<>",SEARCH_CONTAINS) || FindString(MailAddress,"< >",SEARCH_CONTAINS)))
		memset(Storage,0,MaxStorageSize);

	#ifdef TESTING_ADDRESS_LOGGING
	UpdateLogFile("ExtractAddress()",MailAddress,Storage);
	#endif
}

void ReverseResolveAddress(CLIENT_CONTEXT *lpClientContext,char *MailAddress)
{
	char			Domain[MAX_WORK_BUFFER_SIZE],Address[MAX_WORK_BUFFER_SIZE],Buffer[MAX_WORK_BUFFER_SIZE];
	int				Position,Count,SuspectResult = FormatErrors;
	HOSTENT			*HostInfo = NULL;
	BOOL			SuspectDomain = FALSE;

	if (strlen(MailAddress) > 0 && strlen(MailAddress) < sizeof(Buffer)-1)
	{
		memset(Domain,0,sizeof(Domain));
		memset(Address,0,sizeof(Address));
		ExtractAddress(MailAddress,Address,sizeof(Address),FALSE);
		if (strlen(Address) > 0)
		{
			// Find at sign
			Position = strlen(Address)-1;
			while (Address[Position] != '@' && Position >= 0)
				Position--;
			if (Position >= 0 && strlen(&Address[Position]) > 0)
				strcpy_s(Domain,sizeof(Domain),&Address[Position+1]);
			else
				strcpy_s(Domain,sizeof(Domain),Address);

			// Find base domain
			Count = 0;
			Position = strlen(Domain)-1;
			while (Position >= 0 && Count < 2)
			{
				if (Domain[Position] == '.')
					Count++;
				Position--;
			}
			if (Domain[Position+1] == '.')
				Position++;
			strcpy_s(Address,sizeof(Address),&Domain[Position+1]);
		}
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Reverse Resolve Address",Address);
		#endif

		memset(Domain,0,sizeof(Domain));
		if (strlen(lpClientContext->AddressString) > 0)
		{
			HostInfo = ::gethostbyaddr(&lpClientContext->ConnectionAddress.sa_data[2],4,AF_INET);
			if (HostInfo != NULL)
			{
				strcpy_s(Domain,sizeof(Domain),HostInfo->h_name);
				#ifdef TESTING_DETAILED_LOGGING
				UpdateLogFile("SMTP","Reverse Resolve Result",Domain);
				#endif
			}
			else
				strcpy_s(Domain,sizeof(Domain),"HostNotFound11004.com");
			#ifdef TESTING_DETAILED_LOGGING
			UpdateLogFile("SMTP","Failed Reverse Resolve",Address);
			#endif
		}

		if (strlen(Domain) > 0)
		{
			// Check if resolved domain is in domain filter
			strcpy_s(Buffer,sizeof(Buffer),"@");
			strcat_s(Buffer,sizeof(Buffer),Domain);
			CheckDomainFilter(lpClientContext,Buffer,&SuspectDomain,&SuspectResult,BL_SUB_DOMAIN_REVERSE);
			if (!ContinueProcess(lpClientContext,FALSE))
				strcat_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy)," [Reverse Lookup]");
		}
		if (ContinueProcess(lpClientContext,FALSE) && !SuspectDomain)
		{
			if (strlen(Domain) > 0)
			{
				// Find at sign
				Position = strlen(Domain)-1;
				while (Domain[Position] != '@' && Position >= 0)
					Position--;
				if (Position >= 0 && strlen(&Domain[Position]) > 0)
					strcpy_s(Buffer,sizeof(Buffer),&Domain[Position+1]);
				else
					strcpy_s(Buffer,sizeof(Buffer),Domain);

				// Find base domain
				Count = 0;
				Position = strlen(Buffer)-1;
				while (Position >= 0 && Count < 2)
				{
					if (Buffer[Position] == '.')
						Count++;
					Position--;
				}
				if (Buffer[Position+1] == '.')
					Position++;
				strcpy_s(Domain,sizeof(Domain),&Buffer[Position+1]);
			}
			if (strlen(Domain) > 0)
			{
				// Check if resolved domain is in domain filter
				strcpy_s(Buffer,sizeof(Buffer),"@");
				strcat_s(Buffer,sizeof(Buffer),Domain);
				CheckDomainFilter(lpClientContext,Buffer,&SuspectDomain,&SuspectResult,BL_SUB_DOMAIN_REVERSE);
				if (!ContinueProcess(lpClientContext,FALSE))
					strcat_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy)," [Reverse Lookup]");
			}
		}
		if (ContinueProcess(lpClientContext,FALSE) && lpClientContext->SuspectDomain && !SuspectDomain)
		{
			lpClientContext->WhiteList = FALSE;
			lpClientContext->BlackListType = BL_DOMAIN;
			lpClientContext->BlackListSubType = BL_SUB_DOMAIN_SUSPECT;
			lpClientContext->BlackListResult = lpClientContext->SuspectResult;
			sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"Incorrect Reverse Resolution for Suspect Domain");
		}
		if (ContinueProcess(lpClientContext,FALSE) && strlen(Address) > 0 && strlen(Domain) > 0)
		{
			if (_stricmp(Address,Domain) == 0)
				UpdateLogFile(lpClientContext->AddressString,"Reverse Lookup matches Return Address -",Domain);
			else
				UpdateLogFile(lpClientContext->AddressString,"Reverse Lookup of Sending Address -",Domain);
		}
	}
}

BOOL AggressiveResolveAddress(CLIENT_CONTEXT *lpClientContext,char *Address,BYTE *AddressList)
{
	char			Buffer[MAX_WORK_BUFFER_SIZE];
	int				Position,Position2;
	BOOL			HostIPFound = FALSE;
	HOSTENT			*HostComputer;

	if (strlen(Address) > 0 && strlen(Address) < MAX_WORK_BUFFER_SIZE-4)
	{
		strcpy_s(Buffer,sizeof(Buffer),Address);
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile(lpClientContext->AddressString,"Performing lookup of",Buffer);
		#endif
		if ((HostComputer = ::gethostbyname(Buffer)) != NULL)
			HostIPFound = TRUE;
		else
		{
			_time64(&lpClientContext->LastAccess);
			strcpy_s(Buffer,sizeof(Buffer),"www.");
			strcat_s(Buffer,sizeof(Buffer),Address);
			#ifdef TESTING_DETAILED_LOGGING
			UpdateLogFile(lpClientContext->AddressString,"Performing lookup of",Buffer);
			#endif
			if ((HostComputer = ::gethostbyname(Buffer)) != NULL)
				HostIPFound = TRUE;
			else
			{
				_time64(&lpClientContext->LastAccess);
				Position = 0;
				while (!HostIPFound && Position < (int) strlen(Address))
				{
					while (!HostIPFound && Position < (int) strlen(Address) && Address[Position] != '.')
						Position++;
					if (Position < (int) strlen(Address) && Address[Position] == '.')
					{
						Position2 = Position+1;
						while (!HostIPFound && Position2 < (int) strlen(Address) && Address[Position2] != '.')
							Position2++;
					}
					if (Position2 >= (int) strlen(Address) || Address[Position2] != '.')
						Position = (int) strlen(Address);
					else if (Address[Position+1] == 'b' && Address[Position+2] == 'i' && Address[Position+3] == 'z' && Address[Position+4] == '.')
						Position = (int) strlen(Address);
					else if (Address[Position+1] == 'c' && Address[Position+2] == 'o' && Address[Position+3] == 'm' && Address[Position+4] == '.')
						Position = (int) strlen(Address);
					else if (Address[Position+1] == 'c' && Address[Position+2] == 'o' && Address[Position+3] == '.')
						Position = (int) strlen(Address);
					else if (Address[Position+1] == 'e' && Address[Position+2] == 'd' && Address[Position+3] == 'u' && Address[Position+4] == '.')
						Position = (int) strlen(Address);
					else if (Address[Position+1] == 'g' && Address[Position+2] == 'o' && Address[Position+3] == 'v' && Address[Position+4] == '.')
						Position = (int) strlen(Address);
					else if (Address[Position+1] == 'n' && Address[Position+2] == 'e' && Address[Position+3] == 't' && Address[Position+4] == '.')
						Position = (int) strlen(Address);
					else if (Address[Position+1] == 'n' && Address[Position+2] == 'i' && Address[Position+3] == 'i' && Address[Position+4] == '.')
						Position = (int) strlen(Address);
					else if (Address[Position+1] == 'o' && Address[Position+2] == 'r' && Address[Position+3] == 'g' && Address[Position+4] == '.')
						Position = (int) strlen(Address);
					else if (Address[Position+1] == 'p' && Address[Position+2] == 'o' && Address[Position+3] == 'b' && Address[Position+4] == '.')
						Position = (int) strlen(Address);
					if (Position < (int) strlen(Address) && Address[Position] == '.' && Position2 < (int) strlen(Address) && Address[Position2] == '.')
					{
						#ifdef TESTING_DETAILED_LOGGING
						UpdateLogFile(lpClientContext->AddressString,"Performing lookup of",&Address[Position+1]);
						#endif
						if ((HostComputer = ::gethostbyname(&Address[Position+1])) != NULL)
							HostIPFound = TRUE;
						else
						{
							_time64(&lpClientContext->LastAccess);
							strcpy_s(Buffer,sizeof(Buffer),"www.");
							strcat_s(Buffer,sizeof(Buffer),&Address[Position+1]);
							#ifdef TESTING_DETAILED_LOGGING
							UpdateLogFile(lpClientContext->AddressString,"Performing lookup of",Buffer);
							#endif
							if ((HostComputer = ::gethostbyname(Buffer)) != NULL)
								HostIPFound = TRUE;
							else
							{
								_time64(&lpClientContext->LastAccess);
								Position = Position2;
								if (Position < (int) strlen(Address) && Address[Position] == '.')
								{
									Position2 = Position+1;
									while (!HostIPFound && Position2 < (int) strlen(Address) && Address[Position2] != '.')
										Position2++;
								}
								if (Position2 >= (int) strlen(Address) || Address[Position2] != '.')
									Position = (int) strlen(Address);
								else if (Address[Position+1] == 'b' && Address[Position+2] == 'i' && Address[Position+3] == 'z' && Address[Position+4] == '.')
									Position = (int) strlen(Address);
								else if (Address[Position+1] == 'c' && Address[Position+2] == 'o' && Address[Position+3] == 'm' && Address[Position+4] == '.')
									Position = (int) strlen(Address);
								else if (Address[Position+1] == 'c' && Address[Position+2] == 'o' && Address[Position+3] == '.')
									Position = (int) strlen(Address);
								else if (Address[Position+1] == 'e' && Address[Position+2] == 'd' && Address[Position+3] == 'u' && Address[Position+4] == '.')
									Position = (int) strlen(Address);
								else if (Address[Position+1] == 'g' && Address[Position+2] == 'o' && Address[Position+3] == 'v' && Address[Position+4] == '.')
									Position = (int) strlen(Address);
								else if (Address[Position+1] == 'n' && Address[Position+2] == 'e' && Address[Position+3] == 't' && Address[Position+4] == '.')
									Position = (int) strlen(Address);
								else if (Address[Position+1] == 'n' && Address[Position+2] == 'i' && Address[Position+3] == 'i' && Address[Position+4] == '.')
									Position = (int) strlen(Address);
								else if (Address[Position+1] == 'o' && Address[Position+2] == 'r' && Address[Position+3] == 'g' && Address[Position+4] == '.')
									Position = (int) strlen(Address);
								else if (Address[Position+1] == 'p' && Address[Position+2] == 'o' && Address[Position+3] == 'b' && Address[Position+4] == '.')
									Position = (int) strlen(Address);
							}
						}
					}
				}
			}
		}
	}
	if (HostIPFound)
	{
		AddressList[0] = (BYTE) (*(HostComputer->h_addr_list))[0];
		AddressList[1] = (BYTE) (*(HostComputer->h_addr_list))[1];
		AddressList[2] = (BYTE) (*(HostComputer->h_addr_list))[2];
		AddressList[3] = (BYTE) (*(HostComputer->h_addr_list))[3];
	}
	else
	{
		AddressList[0] = 0;
		AddressList[1] = 0;
		AddressList[2] = 0;
		AddressList[3] = 0;
	}
	_time64(&lpClientContext->LastAccess);
	return(HostIPFound);
}

void CheckIPFilter(CLIENT_CONTEXT *lpClientContext)
{
	int				Num1,Num2,Num3,Num4;
	FILTER_ENTRY	*FilterList;

	if (DomainFilters != NULL && ConvertIPString(lpClientContext->AddressString,&Num1,&Num2,&Num3,&Num4))
	{
		EnterCriticalSection(&DomainCriticalSection);
		DomainAccessCount++;
		LeaveCriticalSection(&DomainCriticalSection);
		FilterList = DomainFilters;
		while (ContinueProcess(lpClientContext,TRUE) && FilterList != NULL)
		{
			// Check only IP addresses
			if (FilterList->Filter[1] == '0' && !lpClientContext->PermBlackList)
				if (IPInSubnet((unsigned char) FilterList->Filter[4],(unsigned char) FilterList->Filter[5],(unsigned char) FilterList->Filter[6],(unsigned char) FilterList->Filter[7],(unsigned char) FilterList->Filter[8],(unsigned char) FilterList->Filter[9],(unsigned char) FilterList->Filter[10],(unsigned char) FilterList->Filter[11],Num1,Num2,Num3,Num4))
				{
					if (FilterList->Filter[0] == '0')
					{
						#ifndef TESTING_USE_TEMP_FILE
						if (!lpClientContext->WhiteList)
						{
							lpClientContext->WhiteList = TRUE;
							sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"[%s]",lpClientContext->AddressString);
						}
						#endif
					}
					else if (FilterList->Filter[0] == '3' || FilterList->Filter[0] == '4' || FilterList->Filter[0] == '5' || FilterList->Filter[0] == '6')
					{
						// Suspect IP ranges, suspect recipients, white list recipients and disregarded domains are not valid
					}
					else if (FilterList->Filter[0] == '2' || lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListType == BL_TAG || lpClientContext->BlackListType == BL_FORMAT || lpClientContext->BlackListResult == BL_RESULT_FORWARD)
					{
						if (!lpClientContext->PermBlackList)
						{
							if (FilterList->Filter[0] == '2')
								lpClientContext->PermBlackList = TRUE;
							lpClientContext->BlackListType = BL_IP;
							lpClientContext->BlackListSubType = BL_SUB_IP_CONNECT;
							lpClientContext->BlackListResult = FilterList->Filter[2]-'0';
							if (FilterList->Filter[0] == '2' || !lpClientContext->WhiteList)
								sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"[%s]",lpClientContext->AddressString);
							if (lpClientContext->BlackListResult != BL_RESULT_TURFDIR && lpClientContext->BlackListResult != BL_RESULT_FORWARD && lpClientContext->BlackListResult != BL_RESULT_DELETE)
								lpClientContext->BlackListResult = BL_RESULT_FORWARD;
						}
					}
				}
			FilterList = (FILTER_ENTRY *) FilterList->pvNext;
		}
		EnterCriticalSection(&DomainCriticalSection);
		DomainAccessCount--;
		LeaveCriticalSection(&DomainCriticalSection);
	}
}

void CheckDomainFilter(CLIENT_CONTEXT *lpClientContext,char *MailAddress,BOOL *SuspectDomain,int *SuspectResult,int BlackListSub)
{
	char			Mailbox[MAX_WORK_BUFFER_SIZE],Domain[MAX_WORK_BUFFER_SIZE],Address[MAX_WORK_BUFFER_SIZE],Buffer[MAX_WORK_BUFFER_SIZE];
	int				Position,Num1,Num2,Num3,Num4;
	FILTER_ENTRY	*FilterList = NULL;
	BYTE			h_addr_list[4];
	BOOL			FoundItem = FALSE,HostIPFound = FALSE,KeepLooking,AllowNormalIPBlackList;

	if (strlen(MailAddress) > 0 && strlen(MailAddress) < sizeof(Buffer)-1)
	{
		memset(Mailbox,0,sizeof(Mailbox));
		memset(Domain,0,sizeof(Domain));
		memset(Address,0,sizeof(Address));
		ExtractAddress(MailAddress,Address,sizeof(Address),FALSE);
		if (strlen(Address) > 0)
		{
			// Find at sign
			Position = strlen(Address)-1;
			while (Address[Position] != '@' && Position >= 0)
				Position--;
			if (Position >= 0 && strlen(&Address[Position]) > 0)
				strcpy_s(Domain,sizeof(Domain),&Address[Position+1]);
			if (Position >= 0)
			{
				Address[Position] = '\0';
				strcpy_s(Mailbox,sizeof(Mailbox),Address);
				Address[Position] = '@';
				while (strlen(Mailbox) > 0 && Mailbox[strlen(Mailbox)-1] == ' ' || Mailbox[strlen(Mailbox)-1] == '\r' || Mailbox[strlen(Mailbox)-1] == '\n')
					Mailbox[strlen(Mailbox)-1] = '\0';
			}
		}
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Domain Filter Check",Address);
		#endif

		#ifdef TESTING_FORCE_FULL_PROCESSING
		if (ForwardResolution)
		#else
		if (ForwardResolution && !lpClientContext->WhiteList && !lpClientContext->PermBlackList && (lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListResult == BL_RESULT_FORWARD) && strlen(Domain) > 0)
		#endif
		{
			HostIPFound = AggressiveResolveAddress(lpClientContext,Domain,h_addr_list);
			if (HostIPFound)
			{
				Num1 = h_addr_list[0];
				Num2 = h_addr_list[1];
				Num3 = h_addr_list[2];
				Num4 = h_addr_list[3];
				sprintf_s(Buffer,sizeof(Buffer),"%s resolved to [%d.%d.%d.%d]",Domain,Num1,Num2,Num3,Num4);
				#ifdef TESTING_DETAILED_LOGGING
				UpdateLogFile(lpClientContext->AddressString,"Forward Lookup of",Buffer);
				#endif
			}
		}

		// Compare address with filter list
		EnterCriticalSection(&DomainCriticalSection);
		DomainAccessCount++;
		LeaveCriticalSection(&DomainCriticalSection);
		FilterList = DomainFilters;
		KeepLooking = TRUE;
		AllowNormalIPBlackList = TRUE;
		while (KeepLooking && ContinueProcess(lpClientContext,TRUE) && FilterList != NULL)
		{
			// Check domain names and resolved IP address
			FoundItem = FALSE;
			_time64(&lpClientContext->LastAccess);

			// Ignore suspect recipients, white list recipients and disregarded domains for now
			if (FilterList->Filter[0] != '4' && FilterList->Filter[0] != '5' && FilterList->Filter[0] != '6')
			{
				if (HostIPFound && FilterList->Filter[1] == '0' && !lpClientContext->PermBlackList)
				{
					if (IPInSubnet((unsigned char) FilterList->Filter[4],(unsigned char) FilterList->Filter[5],(unsigned char) FilterList->Filter[6],(unsigned char) FilterList->Filter[7],(unsigned char) FilterList->Filter[8],(unsigned char) FilterList->Filter[9],(unsigned char) FilterList->Filter[10],(unsigned char) FilterList->Filter[11],(unsigned char) h_addr_list[0],(unsigned char) h_addr_list[1],(unsigned char) h_addr_list[2],(unsigned char) h_addr_list[3]))
					{
						if (FilterList->Filter[0] == '0')
						{
							// Do not white list items for this case
							// But if found on white list then do not black list, unless permanent black list item found
							AllowNormalIPBlackList = FALSE;
						}
						else if (FilterList->Filter[0] == '3' || FilterList->Filter[0] == '4' || FilterList->Filter[0] == '5' || FilterList->Filter[0] == '6')
						{
							// Suspect IP ranges, suspect recipients, white list recipients and disregarded domains are not valid
						}
						else if (FilterList->Filter[0] == '2' || lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListType == BL_TAG || lpClientContext->BlackListType == BL_FORMAT || lpClientContext->BlackListResult == BL_RESULT_FORWARD)
						{
							if (AllowNormalIPBlackList || FilterList->Filter[0] == '2')
							{
								if (!lpClientContext->PermBlackList)
								{
									if (FilterList->Filter[0] == '2')
										lpClientContext->PermBlackList = TRUE;
									lpClientContext->BlackListType = BL_IP;
									lpClientContext->BlackListSubType = BL_SUB_IP_DOMAIN;
									lpClientContext->BlackListResult = FilterList->Filter[2]-'0';
									if (FilterList->Filter[0] == '2' || !lpClientContext->WhiteList)
									{
										Num1 = h_addr_list[0];
										Num2 = h_addr_list[1];
										Num3 = h_addr_list[2];
										Num4 = h_addr_list[3];
										sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"%s = [%d.%d.%d.%d] [Forward Lookup]",Domain,Num1,Num2,Num3,Num4);
									}
									if (lpClientContext->BlackListResult != BL_RESULT_TURFDIR && lpClientContext->BlackListResult != BL_RESULT_FORWARD && lpClientContext->BlackListResult != BL_RESULT_DELETE)
										lpClientContext->BlackListResult = BL_RESULT_FORWARD;
								}
								KeepLooking = FALSE;
							}
						}
					}
				}
				if (FilterList->Filter[1] != '0' && strlen(&FilterList->Filter[4]) > 0 && !lpClientContext->PermBlackList)
				{
					strcpy_s(Buffer,sizeof(Buffer),&FilterList->Filter[4]);
					if (Buffer[0] == '@' && strlen(Domain) > 0 && strlen(Buffer) > 1)
					{
						// Compare filter to e-mail domain
						if (strlen(Buffer) > 3 && Buffer[1] == '*' && Buffer[strlen(Buffer)-1] == '*')
						{
							Buffer[strlen(Buffer)-1] = '\0';
							FoundItem = FindString(Domain,&Buffer[2],SEARCH_CONTAINS);
						}
						else if (strlen(Buffer) > 2 && Buffer[1] == '*')
							FoundItem = FindString(Domain,&Buffer[2],SEARCH_SUFFIX);
						else if (strlen(Buffer) > 2 && Buffer[strlen(Buffer)-1] == '*')
						{
							Buffer[strlen(Buffer)-1] = '\0';
							FoundItem = FindString(Domain,&Buffer[1],SEARCH_PREFIX);
						}
						else
							FoundItem = FindString(Domain,&Buffer[1],SEARCH_EXACT);
					}
					else if (Buffer[strlen(Buffer)-1] == '@' && strlen(Mailbox) > 0 && strlen(Buffer) > 1)
					{
						// Compare filter to mailbox name
						Buffer[strlen(Buffer)-1] = '\0';
						if (strlen(Buffer) > 2 && Buffer[0] == '*' && Buffer[strlen(Buffer)-1] == '*')
						{
							Buffer[strlen(Buffer)-1] = '\0';
							FoundItem = FindString(Mailbox,&Buffer[1],SEARCH_CONTAINS);
						}
						else if (strlen(Buffer) > 1 && Buffer[0] == '*')
							FoundItem = FindString(Mailbox,&Buffer[1],SEARCH_SUFFIX);
						else if (strlen(Buffer) > 1 && Buffer[strlen(Buffer)-1] == '*')
						{
							Buffer[strlen(Buffer)-1] = '\0';
							FoundItem = FindString(Mailbox,Buffer,SEARCH_PREFIX);
						}
						else
							FoundItem = FindString(Mailbox,Buffer,SEARCH_EXACT);
					}
					else if (strlen(Address) > 0 && strlen(Buffer) > 0)
					{
						// Compare filter to entire address
						if (strlen(Buffer) > 2 && Buffer[0] == '*' && Buffer[strlen(Buffer)-1] == '*')
						{
							Buffer[strlen(Buffer)-1] = '\0';
							FoundItem = FindString(Address,&Buffer[1],SEARCH_CONTAINS);
						}
						else if (strlen(Buffer) > 1 && Buffer[0] == '*')
							FoundItem = FindString(Address,&Buffer[1],SEARCH_SUFFIX);
						else if (strlen(Address) > 1 && Buffer[strlen(Buffer)-1] == '*')
						{
							Buffer[strlen(Buffer)-1] = '\0';
							FoundItem = FindString(Address,Buffer,SEARCH_PREFIX);
						}
						else
							FoundItem = FindString(Address,Buffer,SEARCH_EXACT);
					}
				}
			}
			if (FoundItem && !lpClientContext->PermBlackList)
			{
				if (FilterList->Filter[0] == '0')
				{
					if (!lpClientContext->WhiteList)
					{
						lpClientContext->WhiteList = TRUE;
						sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"%s",FilterList->Filter);
					}
				}
				else if (FilterList->Filter[0] == '3')
				{
					if (SuspectDomain != NULL)
						*SuspectDomain = TRUE;
					if (SuspectResult != NULL)
						*SuspectResult = FilterList->Filter[2]-'0';
				}
				else if (FilterList->Filter[0] == '2' || lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListType == BL_TAG || lpClientContext->BlackListType == BL_FORMAT || lpClientContext->BlackListResult == BL_RESULT_FORWARD)
				{
					if (!lpClientContext->PermBlackList)
					{
						if (FilterList->Filter[0] == '2')
							lpClientContext->PermBlackList = TRUE;
						lpClientContext->BlackListType = BL_DOMAIN;
						lpClientContext->BlackListSubType = BlackListSub;
						lpClientContext->BlackListResult = FilterList->Filter[2]-'0';
						if (FilterList->Filter[0] == '2' || !lpClientContext->WhiteList)
							sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"%s",FilterList->Filter);
						if (lpClientContext->BlackListResult != BL_RESULT_TURFDIR && lpClientContext->BlackListResult != BL_RESULT_FORWARD && lpClientContext->BlackListResult != BL_RESULT_DELETE)
							lpClientContext->BlackListResult = BL_RESULT_FORWARD;
					}
				}
			}
			FilterList = (FILTER_ENTRY *) FilterList->pvNext;
		}
		EnterCriticalSection(&DomainCriticalSection);
		DomainAccessCount--;
		LeaveCriticalSection(&DomainCriticalSection);
	}
}

void CheckKeywordFilter(CLIENT_CONTEXT *lpClientContext,char *Source,BOOL SubjectLine,BOOL FromField)
{
	FILTER_ENTRY		*FilterList = NULL;
	BOOL				FoundItem;
	long				SourceLength,Position;

	SourceLength = strlen(Source);
	lpClientContext->ScanSize = SourceLength;
	if (SourceLength >= 0)
	{
		#ifdef TESTING_DETAILED_LOGGING
		if (FromField)
			UpdateLogFile(lpClientContext->AddressString,"Keyword From Field Check",Source);
		else if (SubjectLine)
			UpdateLogFile(lpClientContext->AddressString,"Keyword Subject Check",Source);
		else
			UpdateLogFile(lpClientContext->AddressString,"Keyword Body Check",Source);
		#endif

		// Compare string with keyword filter list
		EnterCriticalSection(&KeywordCriticalSection);
		KeywordAccessCount++;
		LeaveCriticalSection(&KeywordCriticalSection);
		Position = 0;
		while (Position < (int) SourceLength)
		{
			lpClientContext->ScanPosition = Position;
			_time64(&lpClientContext->LastAccess);
			YieldControl();
			FilterList = KeywordFilters;
			while ((ContinueProcess(lpClientContext,(SubjectLine || FromField ? TRUE : FALSE)) || ((SubjectLine || FromField) && lpClientContext->BlackListResult != BL_RESULT_DELETE)) && FilterList != NULL)
			{
				FoundItem = FALSE;
				if (FilterList->Filter[3] != '0' && Position > 0)
					FoundItem = FALSE;
				else if ((SubjectLine && FilterList->Filter[1] == '1') || (FromField && FilterList->Filter[1] == '2') || (!SubjectLine && !FromField && FilterList->Filter[2] != '0'))
				{
					if (FilterList->Filter[3] != '0')
						FoundItem = FindString(&Source[Position],&FilterList->Filter[6],SEARCH_EXACT);
					else if (SourceLength-Position >= (int) strlen(&FilterList->Filter[6]) && (FilterList->Filter[6] == '?' || toupper(FilterList->Filter[6]) == toupper(Source[Position])))
						FoundItem = FindString(&Source[Position],&FilterList->Filter[6],SEARCH_PREFIX);
				}
				if (FoundItem && (!lpClientContext->PermBlackList || (FilterList->Filter[0] != '0' && FilterList->Filter[4]-'0' == BL_RESULT_DELETE)))
				{
					if (FilterList->Filter[0] == '0')
					{
						if (!lpClientContext->WhiteList)
						{
							lpClientContext->WhiteList = TRUE;
							sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"%s",FilterList->Filter);
						}
					}
					else if (FilterList->Filter[0] == '2' || lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListType == BL_TAG || lpClientContext->BlackListType == BL_FORMAT || lpClientContext->BlackListResult == BL_RESULT_FORWARD)
					{
						if (!lpClientContext->PermBlackList || (FilterList->Filter[0] != '0' && FilterList->Filter[4]-'0' == BL_RESULT_DELETE))
						{
							if (FilterList->Filter[0] == '2')
								lpClientContext->PermBlackList = TRUE;
							lpClientContext->BlackListType = BL_KEYWORD;
							if (SubjectLine || FromField)
								lpClientContext->BlackListSubType = BL_SUB_KEYWORD_SUBJECT;
							else
								lpClientContext->BlackListSubType = BL_SUB_KEYWORD_BODY;
							lpClientContext->BlackListResult = FilterList->Filter[4]-'0';
							if (FilterList->Filter[0] == '2' || !lpClientContext->WhiteList)
								sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"%s",FilterList->Filter);
							if (lpClientContext->BlackListResult != BL_RESULT_TURFDIR && lpClientContext->BlackListResult != BL_RESULT_FORWARD && lpClientContext->BlackListResult != BL_RESULT_DELETE)
								lpClientContext->BlackListResult = BL_RESULT_FORWARD;
						}
					}
				}
				FilterList = (FILTER_ENTRY *) FilterList->pvNext;
			}
			Position++;
		}
		EnterCriticalSection(&KeywordCriticalSection);
		KeywordAccessCount--;
		LeaveCriticalSection(&KeywordCriticalSection);
	}
}

void CheckWhiteListRecipients(CLIENT_CONTEXT *lpClientContext,char *RecipientAddress,int RecipientPosition)
{
	char			Mailbox[MAX_WORK_BUFFER_SIZE],Domain[MAX_WORK_BUFFER_SIZE],Address[MAX_WORK_BUFFER_SIZE],Buffer[MAX_WORK_BUFFER_SIZE];
	int				Position;
	FILTER_ENTRY	*FilterList = NULL;
	BOOL			FoundItem = FALSE;

	if (lpClientContext->WhiteRecipient < 0 && strlen(RecipientAddress) > 0 && strlen(RecipientAddress) < sizeof(Buffer)-1)
	{
		memset(Mailbox,0,sizeof(Mailbox));
		memset(Domain,0,sizeof(Domain));
		memset(Address,0,sizeof(Address));
		ExtractAddress(RecipientAddress,Address,sizeof(Address),FALSE);
		if (strlen(Address) > 0)
		{
			// Find at sign
			Position = strlen(Address)-1;
			while (Address[Position] != '@' && Position >= 0)
				Position--;
			if (Position >= 0 && strlen(&Address[Position]) > 0)
				strcpy_s(Domain,sizeof(Domain),&Address[Position+1]);
			if (Position >= 0)
			{
				Address[Position] = '\0';
				strcpy_s(Mailbox,sizeof(Mailbox),Address);
				Address[Position] = '@';
				while (strlen(Mailbox) > 0 && Mailbox[strlen(Mailbox)-1] == ' ' || Mailbox[strlen(Mailbox)-1] == '\r' || Mailbox[strlen(Mailbox)-1] == '\n')
					Mailbox[strlen(Mailbox)-1] = '\0';
			}
		}
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","White List Recipient Check",Address);
		#endif

		// Compare address with filter list
		EnterCriticalSection(&DomainCriticalSection);
		DomainAccessCount++;
		LeaveCriticalSection(&DomainCriticalSection);
		FilterList = DomainFilters;
		while (lpClientContext->WhiteRecipient < 0 && FilterList != NULL)
		{
			// Check white list recipient list
			FoundItem = FALSE;
			_time64(&lpClientContext->LastAccess);
			if (FilterList->Filter[0] == '5' && FilterList->Filter[1] != '0' && strlen(&FilterList->Filter[4]) > 0)
			{
				strcpy_s(Buffer,sizeof(Buffer),&FilterList->Filter[4]);
				if (Buffer[0] == '@' && strlen(Domain) > 0 && strlen(Buffer) > 1)
				{
					// Compare filter to e-mail domain
					if (strlen(Buffer) > 3 && Buffer[1] == '*' && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Domain,&Buffer[2],SEARCH_CONTAINS);
					}
					else if (strlen(Buffer) > 2 && Buffer[1] == '*')
						FoundItem = FindString(Domain,&Buffer[2],SEARCH_SUFFIX);
					else if (strlen(Buffer) > 2 && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Domain,&Buffer[1],SEARCH_PREFIX);
					}
					else
						FoundItem = FindString(Domain,&Buffer[1],SEARCH_EXACT);
				}
				else if (Buffer[strlen(Buffer)-1] == '@' && strlen(Mailbox) > 0 && strlen(Buffer) > 1)
				{
					// Compare filter to mailbox name
					Buffer[strlen(Buffer)-1] = '\0';
					if (strlen(Buffer) > 2 && Buffer[0] == '*' && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Mailbox,&Buffer[1],SEARCH_CONTAINS);
					}
					else if (strlen(Buffer) > 1 && Buffer[0] == '*')
						FoundItem = FindString(Mailbox,&Buffer[1],SEARCH_SUFFIX);
					else if (strlen(Buffer) > 1 && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Mailbox,Buffer,SEARCH_PREFIX);
					}
					else
						FoundItem = FindString(Mailbox,Buffer,SEARCH_EXACT);
				}
				else if (strlen(Address) > 0 && strlen(Buffer) > 0)
				{
					// Compare filter to entire address
					if (strlen(Buffer) > 2 && Buffer[0] == '*' && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Address,&Buffer[1],SEARCH_CONTAINS);
					}
					else if (strlen(Buffer) > 1 && Buffer[0] == '*')
						FoundItem = FindString(Address,&Buffer[1],SEARCH_SUFFIX);
					else if (strlen(Address) > 1 && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Address,Buffer,SEARCH_PREFIX);
					}
					else
						FoundItem = FindString(Address,Buffer,SEARCH_EXACT);
				}
			}
			if (FoundItem)
				lpClientContext->WhiteRecipient = RecipientPosition;
			FilterList = (FILTER_ENTRY *) FilterList->pvNext;
		}
		EnterCriticalSection(&DomainCriticalSection);
		DomainAccessCount--;
		LeaveCriticalSection(&DomainCriticalSection);
	}
}

void CheckSuspectRecipients(CLIENT_CONTEXT *lpClientContext,char *RecipientAddress)
{
	char			Mailbox[MAX_WORK_BUFFER_SIZE],Domain[MAX_WORK_BUFFER_SIZE],Address[MAX_WORK_BUFFER_SIZE],Buffer[MAX_WORK_BUFFER_SIZE];
	int				Position;
	FILTER_ENTRY	*FilterList = NULL;
	BOOL			FoundItem = FALSE;

	if (OutbreakCheck && strlen(RecipientAddress) > 0 && strlen(RecipientAddress) < sizeof(Buffer)-1)
	{
		memset(Mailbox,0,sizeof(Mailbox));
		memset(Domain,0,sizeof(Domain));
		memset(Address,0,sizeof(Address));
		ExtractAddress(RecipientAddress,Address,sizeof(Address),FALSE);
		if (strlen(Address) > 0)
		{
			// Find at sign
			Position = strlen(Address)-1;
			while (Address[Position] != '@' && Position >= 0)
				Position--;
			if (Position >= 0 && strlen(&Address[Position]) > 0)
				strcpy_s(Domain,sizeof(Domain),&Address[Position+1]);
			if (Position >= 0)
			{
				Address[Position] = '\0';
				strcpy_s(Mailbox,sizeof(Mailbox),Address);
				Address[Position] = '@';
				while (strlen(Mailbox) > 0 && Mailbox[strlen(Mailbox)-1] == ' ' || Mailbox[strlen(Mailbox)-1] == '\r' || Mailbox[strlen(Mailbox)-1] == '\n')
					Mailbox[strlen(Mailbox)-1] = '\0';
			}
		}
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Outbreak Suspect Recipient Check",Address);
		#endif

		// Compare address with filter list
		EnterCriticalSection(&DomainCriticalSection);
		DomainAccessCount++;
		LeaveCriticalSection(&DomainCriticalSection);
		FilterList = DomainFilters;
		while (ContinueProcess(lpClientContext,TRUE) && FilterList != NULL)
		{
			// Check suspect recipient list
			FoundItem = FALSE;
			_time64(&lpClientContext->LastAccess);
			if (FilterList->Filter[0] == '4' && FilterList->Filter[1] != '0' && strlen(&FilterList->Filter[4]) > 0)
			{
				strcpy_s(Buffer,sizeof(Buffer),&FilterList->Filter[4]);
				if (Buffer[0] == '@' && strlen(Domain) > 0 && strlen(Buffer) > 1)
				{
					// Compare filter to e-mail domain
					if (strlen(Buffer) > 3 && Buffer[1] == '*' && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Domain,&Buffer[2],SEARCH_CONTAINS);
					}
					else if (strlen(Buffer) > 2 && Buffer[1] == '*')
						FoundItem = FindString(Domain,&Buffer[2],SEARCH_SUFFIX);
					else if (strlen(Buffer) > 2 && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Domain,&Buffer[1],SEARCH_PREFIX);
					}
					else
						FoundItem = FindString(Domain,&Buffer[1],SEARCH_EXACT);
				}
				else if (Buffer[strlen(Buffer)-1] == '@' && strlen(Mailbox) > 0 && strlen(Buffer) > 1)
				{
					// Compare filter to mailbox name
					Buffer[strlen(Buffer)-1] = '\0';
					if (strlen(Buffer) > 2 && Buffer[0] == '*' && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Mailbox,&Buffer[1],SEARCH_CONTAINS);
					}
					else if (strlen(Buffer) > 1 && Buffer[0] == '*')
						FoundItem = FindString(Mailbox,&Buffer[1],SEARCH_SUFFIX);
					else if (strlen(Buffer) > 1 && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Mailbox,Buffer,SEARCH_PREFIX);
					}
					else
						FoundItem = FindString(Mailbox,Buffer,SEARCH_EXACT);
				}
				else if (strlen(Address) > 0 && strlen(Buffer) > 0)
				{
					// Compare filter to entire address
					if (strlen(Buffer) > 2 && Buffer[0] == '*' && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Address,&Buffer[1],SEARCH_CONTAINS);
					}
					else if (strlen(Buffer) > 1 && Buffer[0] == '*')
						FoundItem = FindString(Address,&Buffer[1],SEARCH_SUFFIX);
					else if (strlen(Address) > 1 && Buffer[strlen(Buffer)-1] == '*')
					{
						Buffer[strlen(Buffer)-1] = '\0';
						FoundItem = FindString(Address,Buffer,SEARCH_PREFIX);
					}
					else
						FoundItem = FindString(Address,Buffer,SEARCH_EXACT);
				}
			}
			if (FoundItem && !lpClientContext->PermBlackList)
			{
				// White listed messages, at this point, can pass
				if (!lpClientContext->WhiteList)
				{
					// If the message isn't already black listed by IP address then add the IP to the outbreak list
					if (lpClientContext->BlackListType != BL_IP)
						RecordOutbreakTracking(lpClientContext,FilterList->Filter[2]);

					lpClientContext->PermBlackList = TRUE;
					lpClientContext->BlackListType = BL_IP;
					lpClientContext->BlackListSubType = BL_SUB_IP_CONNECT;
					lpClientContext->BlackListResult = FilterList->Filter[2]-'0';
					if (!lpClientContext->WhiteList)
						sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"%s = [%s] [Outbreak]",FilterList->Filter,lpClientContext->AddressString);
					if (lpClientContext->BlackListResult != BL_RESULT_TURFDIR && lpClientContext->BlackListResult != BL_RESULT_FORWARD && lpClientContext->BlackListResult != BL_RESULT_DELETE)
						lpClientContext->BlackListResult = BL_RESULT_FORWARD;
					EnterCriticalSection(&CriticalSection);
					OutbreakCount++;
					LeaveCriticalSection(&CriticalSection);
				}
			}
			FilterList = (FILTER_ENTRY *) FilterList->pvNext;
		}
		EnterCriticalSection(&DomainCriticalSection);
		DomainAccessCount--;
		LeaveCriticalSection(&DomainCriticalSection);
	}
}

void CheckOutbreakFilter(CLIENT_CONTEXT *lpClientContext)
{
	FILTER_ENTRY	*FilterList;
	BOOL			FoundItem = FALSE;

	if (OutbreakCheck && lpClientContext != NULL)
	{
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Outbreak","Filter Check");
		#endif

		// Compare IP address with outbreak list, but do not block if connecting IP is white listed
		EnterCriticalSection(&OutbreakCriticalSection);
		FilterList = OutbreakFilters;
		while (!FoundItem && ContinueProcess(lpClientContext,TRUE) && FilterList != NULL && !lpClientContext->WhiteList)
		{
			// Check only IP addresses
			if (FilterList->Filter[1] == '0' && !lpClientContext->PermBlackList && !lpClientContext->WhiteList)
				if (IPInSubnet((unsigned char) FilterList->Filter[4],(unsigned char) FilterList->Filter[5],(unsigned char) FilterList->Filter[6],(unsigned char) FilterList->Filter[7],(unsigned char) FilterList->Filter[8],(unsigned char) FilterList->Filter[9],(unsigned char) FilterList->Filter[10],(unsigned char) FilterList->Filter[11],(unsigned char) lpClientContext->ConnectionAddress.sa_data[2],(unsigned char) lpClientContext->ConnectionAddress.sa_data[3],(unsigned char) lpClientContext->ConnectionAddress.sa_data[4],(unsigned char) lpClientContext->ConnectionAddress.sa_data[5]))
				{
					FoundItem = TRUE;
					if (FilterList->Filter[0] == '0')
					{
						// Do not white list items for this case
					}
					else if (FilterList->Filter[0] == '3' || FilterList->Filter[0] == '4' || FilterList->Filter[0] == '5' || FilterList->Filter[0] == '6')
					{
						// Suspect IP ranges, suspect recipients, white list recipients and disregarded domains are not valid
					}
					else if (FilterList->Filter[0] == '2' || lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListType == BL_TAG || lpClientContext->BlackListType == BL_FORMAT || lpClientContext->BlackListResult == BL_RESULT_FORWARD)
					{
						if (!lpClientContext->PermBlackList && !lpClientContext->WhiteList)
						{
							if (FilterList->Filter[0] == '2')
								lpClientContext->PermBlackList = TRUE;
							lpClientContext->BlackListType = BL_IP;
							lpClientContext->BlackListSubType = BL_SUB_IP_CONNECT;
							lpClientContext->BlackListResult = FilterList->Filter[2]-'0';
							if (FilterList->Filter[0] == '2' || !lpClientContext->WhiteList)
								sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"[%s] [Outbreak]",lpClientContext->AddressString);
							if (lpClientContext->BlackListResult != BL_RESULT_TURFDIR && lpClientContext->BlackListResult != BL_RESULT_FORWARD && lpClientContext->BlackListResult != BL_RESULT_DELETE)
								lpClientContext->BlackListResult = BL_RESULT_FORWARD;
							EnterCriticalSection(&CriticalSection);
							OutbreakCount++;
							LeaveCriticalSection(&CriticalSection);
						}
					}
				}
			FilterList = (FILTER_ENTRY *) FilterList->pvNext;
		}
		LeaveCriticalSection(&OutbreakCriticalSection);
	}
}

void RecordOutbreakTracking(CLIENT_CONTEXT *lpClientContext,char BlackListResult)
{
	FILTER_ENTRY		*FilterList,*NewEntry;
	int					Num1,Num2,Num3,Num4;
	BOOL				FoundItem,IsBlocked = FALSE;

	if (OutbreakCheck)
	{
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Recording Outbreak Information",lpClientContext->AddressString);
		#endif

		// Compare strings with outbreak entries
		EnterCriticalSection(&OutbreakCriticalSection);
		FoundItem = FALSE;
		FilterList = OutbreakFilters;
		while (FilterList != NULL && !FoundItem)
		{
			_time64(&lpClientContext->LastAccess);
			YieldControl();
			if (IPInSubnet((unsigned char) FilterList->Filter[4],(unsigned char) FilterList->Filter[5],(unsigned char) FilterList->Filter[6],(unsigned char) FilterList->Filter[7],(unsigned char) FilterList->Filter[8],(unsigned char) FilterList->Filter[9],(unsigned char) FilterList->Filter[10],(unsigned char) FilterList->Filter[11],(unsigned char) lpClientContext->ConnectionAddress.sa_data[2],(unsigned char) lpClientContext->ConnectionAddress.sa_data[3],(unsigned char) lpClientContext->ConnectionAddress.sa_data[4],(unsigned char) lpClientContext->ConnectionAddress.sa_data[5]))
				FoundItem = TRUE;
			FilterList = (FILTER_ENTRY *) FilterList->pvNext;
		}
		if (!FoundItem)
		{
			// Check if IP address is already being blocked
			// If so, do not record it in outbreak tracking
			IsBlocked = FALSE;
			Num1 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[2];
			Num2 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[3];
			Num3 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[4];
			Num4 = (unsigned char) lpClientContext->ConnectionAddress.sa_data[5];
			EnterCriticalSection(&DomainCriticalSection);
			DomainAccessCount++;
			LeaveCriticalSection(&DomainCriticalSection);
			FilterList = DomainFilters;
			while (!IsBlocked && FilterList != NULL)
			{
				// Check only IP addresses
				if (FilterList->Filter[1] == '0' && (FilterList->Filter[0] == '2' || FilterList->Filter[0] == '6'))
					if (IPInSubnet((unsigned char) FilterList->Filter[4],(unsigned char) FilterList->Filter[5],(unsigned char) FilterList->Filter[6],(unsigned char) FilterList->Filter[7],(unsigned char) FilterList->Filter[8],(unsigned char) FilterList->Filter[9],(unsigned char) FilterList->Filter[10],(unsigned char) FilterList->Filter[11],Num1,Num2,Num3,Num4))
					{
						if (FilterList->Filter[0] == '0')
						{
							// Ignore white list IP ranges
						}
						else if (FilterList->Filter[0] == '1' || FilterList->Filter[0] == '3' || FilterList->Filter[0] == '4' || FilterList->Filter[0] == '5')
						{
							// Regular black list, suspect IP ranges, suspect recipients and white list recipients are not valid
						}
						else if (FilterList->Filter[0] == '2' || FilterList->Filter[0] == '6')
						{
							IsBlocked = TRUE;
						}
					}
				FilterList = (FILTER_ENTRY *) FilterList->pvNext;
			}
			EnterCriticalSection(&DomainCriticalSection);
			DomainAccessCount--;
			LeaveCriticalSection(&DomainCriticalSection);
		}
		if (!FoundItem && OutbreakLogSize < MaxTrackingSize && !IsBlocked)
		{
			// Add entry to list
			#ifndef MEMORY_NEW_ALLOC
			NewEntry = new FILTER_ENTRY;
			#else
			NewEntry = (FILTER_ENTRY *) AllocateBlock(sizeof(FILTER_ENTRY),FALSE);
			#endif
			if (NewEntry != NULL)
			{
				memset(NewEntry,0,sizeof(FILTER_ENTRY));
				NewEntry->AllocSize = 11;
				#ifndef MEMORY_NEW_ALLOC
				NewEntry->Filter = new char[NewEntry->AllocSize];
				#else
				NewEntry->Filter = (char *) AllocateBlock(NewEntry->AllocSize,FALSE);
				#endif
				if (NewEntry->Filter != NULL)
				{
					memset(NewEntry->Filter,0,11);
					NewEntry->Filter[0] = '2';
					NewEntry->Filter[1] = '0';
					NewEntry->Filter[2] = '0'; //BlackListResult;
					NewEntry->Filter[3] = ' ';
					NewEntry->Filter[4] = (unsigned char) lpClientContext->ConnectionAddress.sa_data[2];
					NewEntry->Filter[5] = (unsigned char) lpClientContext->ConnectionAddress.sa_data[3];
					NewEntry->Filter[6] = (unsigned char) lpClientContext->ConnectionAddress.sa_data[4];
					NewEntry->Filter[7] = (unsigned char) lpClientContext->ConnectionAddress.sa_data[5];
					NewEntry->Filter[8] = (unsigned char) 255;
					NewEntry->Filter[9] = (unsigned char) 255;
					NewEntry->Filter[10] = (unsigned char) 255;
					NewEntry->Filter[11] = (unsigned char) 255;
					NewEntry->pvNext = NULL;
					if (OutbreakFilters != NULL)
						NewEntry->pvNext = OutbreakFilters;
					OutbreakFilters = NewEntry;
					OutbreakLogSize++;
				}
				else
					#ifndef MEMORY_NEW_ALLOC
					delete NewEntry;
					#else
					ReleaseBlock((void *) NewEntry,sizeof(FILTER_ENTRY));
					#endif
			}
		}
		LeaveCriticalSection(&OutbreakCriticalSection);
	}
}

void RecordIPTracking(CLIENT_CONTEXT *lpClientContext)
{
	FILTER_ENTRY		*FilterList = NULL,*NewEntry,*ReplaceEntry[4],*PreviousEntry;
	BOOL				FoundItem[4],AllFound,IsBlocked = FALSE;
	int					Loop,Loop2,AddrNum,Num1,Num2,Num3,Num4,AllocSize;
	long				CurrentCount;
	char				Source[4][30],*NewFilter;

	for (Loop = 0; Loop < 4; Loop++)
		ReplaceEntry[Loop] = NULL;
	if (lpClientContext->HTMLAddrCount <= MAX_HTML_RECORDS)
	{
		lpClientContext->HTMLAddr[lpClientContext->HTMLAddrCount][0] = (unsigned char) lpClientContext->ConnectionAddress.sa_data[2];
		lpClientContext->HTMLAddr[lpClientContext->HTMLAddrCount][1] = (unsigned char) lpClientContext->ConnectionAddress.sa_data[3];
		lpClientContext->HTMLAddr[lpClientContext->HTMLAddrCount][2] = (unsigned char) lpClientContext->ConnectionAddress.sa_data[4];
		lpClientContext->HTMLAddr[lpClientContext->HTMLAddrCount][3] = (unsigned char) lpClientContext->ConnectionAddress.sa_data[5];
		lpClientContext->HTMLAddrCount++;
	}
	if (strlen(TrackingLogFile) > 0)
	{
		for (AddrNum = 0; AddrNum < lpClientContext->HTMLAddrCount; AddrNum++)
			if (lpClientContext->HTMLAddr[AddrNum][0] > 0 || lpClientContext->HTMLAddr[AddrNum][1] > 0 || lpClientContext->HTMLAddr[AddrNum][2] > 0 || lpClientContext->HTMLAddr[AddrNum][3] > 0)
			{
				sprintf_s(Source[0],sizeof(Source[0]),"%d.All",lpClientContext->HTMLAddr[AddrNum][0]);
				sprintf_s(Source[1],sizeof(Source[1]),"%d.%d.All",lpClientContext->HTMLAddr[AddrNum][0],lpClientContext->HTMLAddr[AddrNum][1]);
				sprintf_s(Source[2],sizeof(Source[2]),"%d.%d.%d.All",lpClientContext->HTMLAddr[AddrNum][0],lpClientContext->HTMLAddr[AddrNum][1],lpClientContext->HTMLAddr[AddrNum][2]);
				sprintf_s(Source[3],sizeof(Source[3]),"%d.%d.%d.%d",lpClientContext->HTMLAddr[AddrNum][0],lpClientContext->HTMLAddr[AddrNum][1],lpClientContext->HTMLAddr[AddrNum][2],lpClientContext->HTMLAddr[AddrNum][3]);
				#ifdef TESTING_DETAILED_LOGGING
				UpdateLogFile("SMTP","Proving IP Tracking Information",Source[3]);
				#endif

				// Check if IP address is already being blocked
				// If so, do not record it in tracking log
				IsBlocked = FALSE;
				Num1 = lpClientContext->HTMLAddr[AddrNum][0];
				Num2 = lpClientContext->HTMLAddr[AddrNum][1];
				Num3 = lpClientContext->HTMLAddr[AddrNum][2];
				Num4 = lpClientContext->HTMLAddr[AddrNum][3];
				EnterCriticalSection(&DomainCriticalSection);
				DomainAccessCount++;
				LeaveCriticalSection(&DomainCriticalSection);
				FilterList = DomainFilters;
				while (!IsBlocked && FilterList != NULL)
				{
					// Check only IP addresses
					if (FilterList->Filter[1] == '0' && (FilterList->Filter[0] == '1' || FilterList->Filter[0] == '2' || FilterList->Filter[0] == '6'))
						if (IPInSubnet((unsigned char) FilterList->Filter[4],(unsigned char) FilterList->Filter[5],(unsigned char) FilterList->Filter[6],(unsigned char) FilterList->Filter[7],(unsigned char) FilterList->Filter[8],(unsigned char) FilterList->Filter[9],(unsigned char) FilterList->Filter[10],(unsigned char) FilterList->Filter[11],Num1,Num2,Num3,Num4))
						{
							if (FilterList->Filter[0] == '0')
							{
								// Ignore white list IP ranges
							}
							else if (FilterList->Filter[0] == '3' || FilterList->Filter[0] == '4' || FilterList->Filter[0] == '5')
							{
								// Suspect IP ranges, suspect recipients and white list recipients are not valid
							}
							else if (FilterList->Filter[0] == '1' || FilterList->Filter[0] == '2' || FilterList->Filter[0] == '6')
							{
								IsBlocked = TRUE;
							}
						}
					FilterList = (FILTER_ENTRY *) FilterList->pvNext;
				}
				EnterCriticalSection(&DomainCriticalSection);
				DomainAccessCount--;
				LeaveCriticalSection(&DomainCriticalSection);

				if (!IsBlocked)
				{
					#ifdef TESTING_DETAILED_LOGGING
					UpdateLogFile("SMTP","Recording IP Tracking Information",Source[3]);
					#endif

					// Compare strings with tracking log entries
					EnterCriticalSection(&TrackingCriticalSection);
					for (Loop = 0; Loop < 4; Loop++)
						FoundItem[Loop] = FALSE;
					FoundItem[0] = TRUE;
					FoundItem[1] = TRUE;
					AllFound = FALSE;
					FilterList = TrackingLog;
					while (FilterList != NULL && !AllFound)
					{
						_time64(&lpClientContext->LastAccess);
						YieldControl();
						if (ReplaceEntry[0] == NULL)
							ReplaceEntry[0] = FilterList;
						else if (atol(FilterList->Filter) <= atol(ReplaceEntry[0]->Filter))
						{
							for (Loop = 3; Loop > 0; Loop--)
								ReplaceEntry[Loop] = ReplaceEntry[Loop-1];
							ReplaceEntry[0] = FilterList;
						}
						for (Loop = 0; !AllFound && Loop < 4; Loop++)
							if (!FoundItem[Loop])
							{
								FoundItem[Loop] = FindString(Source[Loop],&FilterList->Filter[6],SEARCH_EXACT);
								if (FoundItem[Loop])
								{
									// Update count for entry
									CurrentCount = atol(FilterList->Filter);
									CurrentCount++;
									if (CurrentCount >= 100000)
										CurrentCount = 99999;
									sprintf_s(FilterList->Filter,strlen(FilterList->Filter)+1,"%05d %s",CurrentCount,Source[Loop]);

									AllFound = TRUE;
									for (Loop2 = 0; AllFound && Loop2 < 4; Loop2++)
										if (!FoundItem[Loop2])
											AllFound = FALSE;
								}
							}
						FilterList = (FILTER_ENTRY *) FilterList->pvNext;
					}
					for (Loop = 0; Loop < 4; Loop++)
						if (!FoundItem[Loop] && TrackingLogSize < MaxTrackingSize)
						{
							// Add entry to list
							#ifndef MEMORY_NEW_ALLOC
							NewEntry = new FILTER_ENTRY;
							#else
							NewEntry = (FILTER_ENTRY *) AllocateBlock(sizeof(FILTER_ENTRY),FALSE);
							#endif
							if (NewEntry != NULL)
							{
								memset(NewEntry,0,sizeof(FILTER_ENTRY));
								NewEntry->AllocSize = strlen(Source[Loop])+7;
								#ifndef MEMORY_NEW_ALLOC
								NewEntry->Filter = new char[NewEntry->AllocSize];
								#else
								NewEntry->Filter = (char *) AllocateBlock(NewEntry->AllocSize,FALSE);
								#endif
								if (NewEntry->Filter != NULL)
								{
									sprintf_s(NewEntry->Filter,strlen(Source[Loop])+7,"%05d %s",1,Source[Loop]);
									NewEntry->pvNext = NULL;
									if (TrackingLog != NULL)
										NewEntry->pvNext = TrackingLog;
									TrackingLog = NewEntry;
									TrackingLogSize++;
								}
								else
									#ifndef MEMORY_NEW_ALLOC
									delete NewEntry;
									#else
									ReleaseBlock((void *) NewEntry,sizeof(FILTER_ENTRY));
									#endif
							}
						}
						else if (!FoundItem[Loop] && TrackingLogSize >= MaxTrackingSize && ReplaceEntry[Loop] != NULL)
						{
							// Replace existing entry in list with new information
							PreviousEntry = TrackingLog;
							while (PreviousEntry != NULL && PreviousEntry->pvNext != ReplaceEntry[Loop])
								PreviousEntry = (FILTER_ENTRY *) PreviousEntry->pvNext;
							if (PreviousEntry != NULL)
							{
								AllocSize = strlen(Source[Loop])+7;
								#ifndef MEMORY_NEW_ALLOC
								NewFilter = new char[AllocSize];
								#else
								NewFilter = (char *) AllocateBlock(AllocSize,FALSE);
								#endif
								if (NewFilter != NULL)
								{
									sprintf_s(NewFilter,strlen(Source[Loop])+7,"%05d %s",1,Source[Loop]);
									#ifndef MEMORY_NEW_ALLOC
									delete [] ReplaceEntry[Loop]->Filter;
									#else
									ReleaseBlock((void *) ReplaceEntry[Loop]->Filter,ReplaceEntry[Loop]->AllocSize);
									#endif
									ReplaceEntry[Loop]->AllocSize = AllocSize;
									ReplaceEntry[Loop]->Filter = NewFilter;
									PreviousEntry->pvNext = ReplaceEntry[Loop]->pvNext;
									ReplaceEntry[Loop]->pvNext = NULL;
									if (TrackingLog != NULL)
										ReplaceEntry[Loop]->pvNext = TrackingLog;
									TrackingLog = ReplaceEntry[Loop];
								}
							}
						}
					LeaveCriticalSection(&TrackingCriticalSection);
				}
			}
	}
}

void RecordDomainTracking(CLIENT_CONTEXT *lpClientContext)
{
	char				*DomainPosition = NULL,Buffer[MAX_KEYWORD_SIZE],*NewFilter,WorkBuffer[MAX_WORK_BUFFER_SIZE];
	FILTER_ENTRY		*FilterList,*NewEntry,*ReplaceEntry,*PreviousEntry;
	BOOL				FoundItem,IsBlocked = FALSE;
	int					AllocSize;
	long				CurrentCount;

	ReplaceEntry = NULL;
	if (strlen(TrackingLogFile) > 0 && strlen(lpClientContext->FromField) > 0)
	{
		strcpy_s(Buffer,sizeof(Buffer),lpClientContext->FromField);
		DomainPosition = &Buffer[strlen(Buffer)-1];
		while (DomainPosition >= Buffer && *DomainPosition != '@')
			DomainPosition--;
		if (*DomainPosition == '@')
			DomainPosition++;
		while (strlen(DomainPosition) > 0 && (DomainPosition[strlen(DomainPosition)-1] == '>' || DomainPosition[strlen(DomainPosition)-1] == ' ' || DomainPosition[strlen(DomainPosition)-1] == '.'))
			DomainPosition[strlen(DomainPosition)-1] = '\0';
		if (strlen(DomainPosition) > 0)
		{
			#ifdef TESTING_DETAILED_LOGGING
			UpdateLogFile("SMTP","Recording Domain Tracking Information",DomainPosition);
			#endif

			// Compare string with tracking log entries
			EnterCriticalSection(&TrackingCriticalSection);
			FoundItem = FALSE;
			FilterList = TrackingLog;
			while (FilterList != NULL && !FoundItem)
			{
				_time64(&lpClientContext->LastAccess);
				YieldControl();
				if (ReplaceEntry == NULL)
					ReplaceEntry = FilterList;
				else if (atol(FilterList->Filter) <= atol(ReplaceEntry->Filter))
					ReplaceEntry = FilterList;
				FoundItem = FindString(DomainPosition,&FilterList->Filter[6],SEARCH_EXACT);
				if (FoundItem)
				{
					// Update count for entry
					CurrentCount = atol(FilterList->Filter);
					CurrentCount++;
					if (CurrentCount >= 100000)
						CurrentCount = 99999;
					sprintf_s(FilterList->Filter,strlen(FilterList->Filter)+1,"%05d %s",CurrentCount,DomainPosition);
				}
				FilterList = (FILTER_ENTRY *) FilterList->pvNext;
			}
			if (!FoundItem)
			{
				// Check if domain is already being blocked
				// If so, do not record it in domain tracking
				IsBlocked = FALSE;
				EnterCriticalSection(&DomainCriticalSection);
				DomainAccessCount++;
				LeaveCriticalSection(&DomainCriticalSection);
				FilterList = DomainFilters;
				while (!IsBlocked && FilterList != NULL)
				{
					// Check only domain addresses
					if (FilterList->Filter[1] == '1' && (FilterList->Filter[0] == '1' || FilterList->Filter[0] == '2' || FilterList->Filter[0] == '6'))
					{
						strcpy_s(WorkBuffer,sizeof(WorkBuffer),&FilterList->Filter[4]);
						if (WorkBuffer[0] == '@' && strlen(DomainPosition) > 0 && strlen(WorkBuffer) > 1)
						{
							// Compare filter to e-mail domain
							if (strlen(WorkBuffer) > 3 && WorkBuffer[1] == '*' && WorkBuffer[strlen(WorkBuffer)-1] == '*')
							{
								WorkBuffer[strlen(WorkBuffer)-1] = '\0';
								IsBlocked = FindString(DomainPosition,&WorkBuffer[2],SEARCH_CONTAINS);
							}
							else if (strlen(WorkBuffer) > 2 && WorkBuffer[1] == '*')
								IsBlocked = FindString(DomainPosition,&WorkBuffer[2],SEARCH_SUFFIX);
							else if (strlen(WorkBuffer) > 2 && WorkBuffer[strlen(WorkBuffer)-1] == '*')
							{
								WorkBuffer[strlen(WorkBuffer)-1] = '\0';
								IsBlocked = FindString(DomainPosition,&WorkBuffer[1],SEARCH_PREFIX);
							}
							else
								IsBlocked = FindString(DomainPosition,&WorkBuffer[1],SEARCH_EXACT);
						}
					}
					FilterList = (FILTER_ENTRY *) FilterList->pvNext;
				}
				EnterCriticalSection(&DomainCriticalSection);
				DomainAccessCount--;
				LeaveCriticalSection(&DomainCriticalSection);
			}
			if (!IsBlocked)
			{
				if (!FoundItem && TrackingLogSize < MaxTrackingSize)
				{
					// Add entry to list
					#ifndef MEMORY_NEW_ALLOC
					NewEntry = new FILTER_ENTRY;
					#else
					NewEntry = (FILTER_ENTRY *) AllocateBlock(sizeof(FILTER_ENTRY),FALSE);
					#endif
					if (NewEntry != NULL)
					{
						memset(NewEntry,0,sizeof(FILTER_ENTRY));
						NewEntry->AllocSize = strlen(DomainPosition)+7;
						#ifndef MEMORY_NEW_ALLOC
						NewEntry->Filter = new char[NewEntry->AllocSize];
						#else
						NewEntry->Filter = (char *) AllocateBlock(NewEntry->AllocSize,FALSE);
						#endif
						if (NewEntry->Filter != NULL)
						{
							sprintf_s(NewEntry->Filter,strlen(DomainPosition)+7,"%05d %s",1,DomainPosition);
							NewEntry->pvNext = NULL;
							if (TrackingLog != NULL)
								NewEntry->pvNext = TrackingLog;
							TrackingLog = NewEntry;
							TrackingLogSize++;
						}
						else
							#ifndef MEMORY_NEW_ALLOC
							delete NewEntry;
							#else
							ReleaseBlock((void *) NewEntry,sizeof(FILTER_ENTRY));
							#endif
					}
				}
				else if (!FoundItem && TrackingLogSize >= MaxTrackingSize && ReplaceEntry != NULL)
				{
					// Replace existing entry in list with new information
					PreviousEntry = TrackingLog;
					while (PreviousEntry != NULL && PreviousEntry->pvNext != ReplaceEntry)
						PreviousEntry = (FILTER_ENTRY *) PreviousEntry->pvNext;
					if (PreviousEntry != NULL)
					{
						AllocSize = strlen(DomainPosition)+7;
						#ifndef MEMORY_NEW_ALLOC
						NewFilter = new char[AllocSize];
						#else
						NewFilter = (char *) AllocateBlock(AllocSize,FALSE);
						#endif
						if (NewFilter != NULL)
						{
							sprintf_s(NewFilter,strlen(DomainPosition)+7,"%05d %s",1,DomainPosition);
							#ifndef MEMORY_NEW_ALLOC
							delete [] ReplaceEntry->Filter;
							#else
							ReleaseBlock((void *) ReplaceEntry->Filter,ReplaceEntry->AllocSize);
							#endif
							ReplaceEntry->AllocSize = AllocSize;
							ReplaceEntry->Filter = NewFilter;
							PreviousEntry->pvNext = ReplaceEntry->pvNext;
							ReplaceEntry->pvNext = NULL;
							if (TrackingLog != NULL)
								ReplaceEntry->pvNext = TrackingLog;
							TrackingLog = ReplaceEntry;
						}
						else
							ReplaceEntry->AllocSize = 0;
					}
				}
			}
			LeaveCriticalSection(&TrackingCriticalSection);
		}
	}
}

BOOL FindString(char *Source,char *ToFind,int SearchType)
{
	int		SourcePosition,FindPosition;
	BOOL	FoundItem = FALSE,ValidChar = TRUE;
	long	SourceLength,ToFindLength;

	SourceLength = strlen(Source);
	ToFindLength = strlen(ToFind);
	if (SourceLength > 0 && ToFindLength > 0 && SourceLength >= ToFindLength)
		switch (SearchType)
		{
			case SEARCH_PREFIX:		SourcePosition = 0;
									FindPosition = 0;
									ValidChar = TRUE;
									while (!FoundItem && ValidChar && FindPosition < ToFindLength)
									{
										if (ToFind[FindPosition] != '?' && toupper(ToFind[FindPosition]) != toupper(Source[SourcePosition+FindPosition]))
											ValidChar = FALSE;
										FindPosition++;
										if (ValidChar && FindPosition == ToFindLength)
											FoundItem = TRUE;
									}
									break;
			case SEARCH_SUFFIX:		SourcePosition = SourceLength-ToFindLength;
									FindPosition = 0;
									ValidChar = TRUE;
									while (!FoundItem && ValidChar && FindPosition < ToFindLength)
									{
										if (ToFind[FindPosition] != '?' && toupper(ToFind[FindPosition]) != toupper(Source[SourcePosition+FindPosition]))
											ValidChar = FALSE;
										FindPosition++;
										if (ValidChar && FindPosition == ToFindLength)
											FoundItem = TRUE;
									}
									break;
			case SEARCH_EXACT:		if (SourceLength == ToFindLength)
									{
										SourcePosition = 0;
										FindPosition = 0;
										ValidChar = TRUE;
										while (!FoundItem && ValidChar && FindPosition < ToFindLength)
										{
											if (ToFind[FindPosition] != '?' && toupper(ToFind[FindPosition]) != toupper(Source[SourcePosition+FindPosition]))
												ValidChar = FALSE;
											FindPosition++;
											if (ValidChar && FindPosition == ToFindLength)
												FoundItem = TRUE;
										}
									}
									break;
			case SEARCH_CONTAINS:
			default:				SourcePosition = 0;
									while (!FoundItem && SourcePosition <= SourceLength-ToFindLength)
									{
										FindPosition = 0;
										ValidChar = TRUE;
										while (!FoundItem && ValidChar && FindPosition < ToFindLength)
										{
											if (ToFind[FindPosition] != '?' && toupper(ToFind[FindPosition]) != toupper(Source[SourcePosition+FindPosition]))
												ValidChar = FALSE;
											else
											{
												FindPosition++;
												if (FindPosition == ToFindLength)
													FoundItem = TRUE;
											}
										}
										SourcePosition++;
									}
									break;
		}
	return(FoundItem);
}

BOOL RemoveHTMLLinkSpace(CLIENT_CONTEXT *lpClientContext,char *Source)
{
	BOOL			StringChanged = FALSE,InsideTag = FALSE,InsideQuotes = FALSE,LinkFound = FALSE;
	int				CurrentPosition = 0,WritePosition = 0,SourceLen;

	// If an HTML link was broken up onto several lines then remove the spaces that resulted from the line breaks
	#ifdef TESTING_DETAILED_LOGGING
	UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Repairing fragmented HTTP links");
	#endif
	SourceLen = strlen(Source);
	if (SourceLen > 1)
	{
		while (CurrentPosition < SourceLen)
		{
			if (Source[CurrentPosition] == '<' && Source[CurrentPosition+1] != ' ' && (Source[CurrentPosition+1] < '0' || Source[CurrentPosition+1] > '9'))
			{
				InsideTag = TRUE;
				LinkFound = FALSE;
				InsideQuotes = FALSE;
			}
			else if (InsideTag && !InsideQuotes && Source[CurrentPosition] == '>')
			{
				InsideTag = FALSE;
				LinkFound = FALSE;
				InsideQuotes = FALSE;
			}
			else if (InsideTag && !InsideQuotes && (Source[CurrentPosition] == 34 || Source[CurrentPosition] == '\''))
				InsideQuotes = TRUE;
			else if (InsideTag && InsideQuotes && (Source[CurrentPosition] == 34 || Source[CurrentPosition] == '\''))
			{
				InsideQuotes = FALSE;
				LinkFound = FALSE;
			}
			else
			{
				if (InsideTag && toupper(Source[CurrentPosition]) == 'A' && toupper(Source[CurrentPosition+1]) == ' ' && toupper(Source[CurrentPosition+2]) == 'H' && toupper(Source[CurrentPosition+3]) == 'R' && toupper(Source[CurrentPosition+4]) == 'E' && toupper(Source[CurrentPosition+5]) == 'F' && toupper(Source[CurrentPosition+6]) == '=')
					LinkFound = TRUE;
				else if (toupper(Source[CurrentPosition]) == 'H' && toupper(Source[CurrentPosition+1]) == 'T' && toupper(Source[CurrentPosition+2]) == 'T' && toupper(Source[CurrentPosition+3]) == 'P' && Source[CurrentPosition+4] == ':' && (Source[CurrentPosition+5] == '/' || Source[CurrentPosition+5] == '\\') && (Source[CurrentPosition+6] == '/' || Source[CurrentPosition+6] == '\\'))
					LinkFound = TRUE;
				else if (toupper(Source[CurrentPosition]) == 'H' && toupper(Source[CurrentPosition+1]) == 'T' && toupper(Source[CurrentPosition+2]) == 'T' && toupper(Source[CurrentPosition+3]) == 'P' && toupper(Source[CurrentPosition+4]) == 'S' && Source[CurrentPosition+5] == ':' && (Source[CurrentPosition+6] == '/' || Source[CurrentPosition+6] == '\\') && (Source[CurrentPosition+7] == '/' || Source[CurrentPosition+7] == '\\'))
					LinkFound = TRUE;
				else if (toupper(Source[CurrentPosition]) == 'W' && toupper(Source[CurrentPosition+1]) == 'W' && toupper(Source[CurrentPosition+2]) == 'W' && toupper(Source[CurrentPosition+3]) == '.')
					LinkFound = TRUE;
				if (InsideTag && InsideQuotes && LinkFound)
				{
					while (CurrentPosition < SourceLen && toupper(Source[CurrentPosition]) == ' ')
						CurrentPosition++;
					if (CurrentPosition != WritePosition)
					{
						Source[WritePosition] = Source[CurrentPosition];
						StringChanged = TRUE;
					}
					if (Source[CurrentPosition] == 34 || Source[CurrentPosition] == '\'')
					{
						InsideQuotes = FALSE;
						LinkFound = FALSE;
					}
				}
			}
			if (CurrentPosition != WritePosition)
			{
				Source[WritePosition] = Source[CurrentPosition];
				StringChanged = TRUE;
			}
			CurrentPosition++;
			WritePosition++;
		}
		if (StringChanged)
			Source[WritePosition] = '\0';
	}
	return(StringChanged);
}

BOOL RemoveExtraSpace(CLIENT_CONTEXT *lpClientContext,char *Source,BOOL CheckHTMLLinks,BOOL IPWhiteList)
{
	BOOL			StringChanged = FALSE,InsideTag = FALSE,InsideQuotes = FALSE,InsideBrackets = FALSE,SpaceFound,AddrFound,KeepLooking;
	int				CurrentPosition = 0,WritePosition = 0,SourceLen,HTMLPosition,HTMLLinkLength[2],NumLinks,Loop,Loop2,Count,RunningCount,Num1,Num2,Num3,Num4;
	char			HTMLLink[2][MAX_MESSAGE_BUFFER],LastHTMLLink[MAX_MESSAGE_BUFFER],Buffer[MAX_WORK_BUFFER_SIZE];
	FILTER_ENTRY	*FilterList = NULL;
	BYTE			h_addr_list[4];

	// Remove all HTML tags and extra spaces in the string
	memset(LastHTMLLink,0,sizeof(LastHTMLLink));
	SourceLen = strlen(Source);
	if (SourceLen > 1)
	{
		while (CurrentPosition < SourceLen && Source[CurrentPosition] == ' ')
			CurrentPosition++;
		while (CurrentPosition < SourceLen)
		{
			if (Source[CurrentPosition] == '<' && Source[CurrentPosition+1] != ' ' && (Source[CurrentPosition+1] < '0' || Source[CurrentPosition+1] > '9'))
			{
				InsideTag = TRUE;
				InsideQuotes = FALSE;
			}
			else if (InsideTag && !InsideQuotes && Source[CurrentPosition] == '>')
			{
				InsideTag = FALSE;
				InsideQuotes = FALSE;
			}
			else if (InsideTag && !InsideQuotes && (Source[CurrentPosition] == 34 || Source[CurrentPosition] == '\''))
				InsideQuotes = TRUE;
			else if (InsideTag && InsideQuotes && (Source[CurrentPosition] == 34 || Source[CurrentPosition] == '\''))
				InsideQuotes = FALSE;
			else
			{
				while (CurrentPosition < SourceLen-1 && Source[CurrentPosition] == ' ' && Source[CurrentPosition+1] == ' ')
					CurrentPosition++;
				#ifdef TESTING_FORCE_FULL_PROCESSING
				if (CheckHTMLLinks && ForwardResolution)
				#else
				if (CheckHTMLLinks && ForwardResolution && (!lpClientContext->WhiteList || !IPWhiteList) && !lpClientContext->PermBlackList && (lpClientContext->WhiteList || lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListResult == BL_RESULT_FORWARD))
				#endif
				{
					NumLinks = 0;
					for (Loop = 0; Loop < 2; Loop++)
						HTMLLink[Loop][0] = '\0';
					HTMLPosition = -1;
					if (InsideTag && toupper(Source[CurrentPosition]) == 'A' && toupper(Source[CurrentPosition+1]) == ' ' && toupper(Source[CurrentPosition+2]) == 'H' && toupper(Source[CurrentPosition+3]) == 'R' && toupper(Source[CurrentPosition+4]) == 'E' && toupper(Source[CurrentPosition+5]) == 'F' && Source[CurrentPosition+6] == '=' && (Source[CurrentPosition+7] == 34 || Source[CurrentPosition+7] == '\''))
					{
						InsideQuotes = TRUE;
						HTMLPosition = CurrentPosition+8;
						if (toupper(Source[HTMLPosition]) == 'H' && toupper(Source[HTMLPosition+1]) == 'T' && toupper(Source[HTMLPosition+2]) == 'T' && toupper(Source[HTMLPosition+3]) == 'P' && Source[HTMLPosition+4] == ':' && (Source[HTMLPosition+5] == '/' || Source[HTMLPosition+5] == '\\') && (Source[HTMLPosition+6] == '/' || Source[HTMLPosition+6] == '\\'))
						{
							HTMLPosition += 7;
							CurrentPosition += 8;
							if (toupper(Source[HTMLPosition]) == 'W' && toupper(Source[HTMLPosition+1]) == 'W' && toupper(Source[HTMLPosition+2]) == 'W' && toupper(Source[HTMLPosition+3]) == '.' && toupper(Source[HTMLPosition+4]) != '.')
								CurrentPosition += 7;
						}
						else if (toupper(Source[HTMLPosition]) == 'H' && toupper(Source[HTMLPosition+1]) == 'T' && toupper(Source[HTMLPosition+2]) == 'T' && toupper(Source[HTMLPosition+3]) == 'P' && toupper(Source[HTMLPosition+4]) == 'S' && Source[HTMLPosition+5] == ':' && (Source[HTMLPosition+6] == '/' || Source[HTMLPosition+6] == '\\') && (Source[HTMLPosition+7] == '/' || Source[HTMLPosition+7] == '\\'))
						{
							HTMLPosition += 8;
							CurrentPosition += 8;
							if (toupper(Source[HTMLPosition]) == 'W' && toupper(Source[HTMLPosition+1]) == 'W' && toupper(Source[HTMLPosition+2]) == 'W' && toupper(Source[HTMLPosition+3]) == '.' && toupper(Source[HTMLPosition+4]) != '.')
								CurrentPosition += 8;
						}
						else if (toupper(Source[HTMLPosition]) == 'W' && toupper(Source[HTMLPosition+1]) == 'W' && toupper(Source[HTMLPosition+2]) == 'W' && toupper(Source[HTMLPosition+3]) == '.' && toupper(Source[HTMLPosition+4]) != '.')
							CurrentPosition += 8;
					}
					else if (InsideTag && toupper(Source[CurrentPosition]) == 'A' && toupper(Source[CurrentPosition+1]) == ' ' && toupper(Source[CurrentPosition+2]) == 'H' && toupper(Source[CurrentPosition+3]) == 'R' && toupper(Source[CurrentPosition+4]) == 'E' && toupper(Source[CurrentPosition+5]) == 'F' && Source[CurrentPosition+6] == '=')
					{
						InsideQuotes = FALSE;
						HTMLPosition = CurrentPosition+7;
						if (toupper(Source[HTMLPosition]) == 'H' && toupper(Source[HTMLPosition+1]) == 'T' && toupper(Source[HTMLPosition+2]) == 'T' && toupper(Source[HTMLPosition+3]) == 'P' && Source[HTMLPosition+4] == ':' && (Source[HTMLPosition+5] == '/' || Source[HTMLPosition+5] == '\\') && (Source[HTMLPosition+6] == '/' || Source[HTMLPosition+6] == '\\'))
						{
							HTMLPosition += 7;
							CurrentPosition += 7;
							if (toupper(Source[HTMLPosition]) == 'W' && toupper(Source[HTMLPosition+1]) == 'W' && toupper(Source[HTMLPosition+2]) == 'W' && toupper(Source[HTMLPosition+3]) == '.' && toupper(Source[HTMLPosition+4]) != '.')
								CurrentPosition += 7;
						}
						else if (toupper(Source[HTMLPosition]) == 'H' && toupper(Source[HTMLPosition+1]) == 'T' && toupper(Source[HTMLPosition+2]) == 'T' && toupper(Source[HTMLPosition+3]) == 'P' && toupper(Source[HTMLPosition+4]) == 'S' && Source[HTMLPosition+5] == ':' && (Source[HTMLPosition+6] == '/' || Source[HTMLPosition+6] == '\\') && (Source[HTMLPosition+7] == '/' || Source[HTMLPosition+7] == '\\'))
						{
							HTMLPosition += 8;
							CurrentPosition += 7;
							if (toupper(Source[HTMLPosition]) == 'W' && toupper(Source[HTMLPosition+1]) == 'W' && toupper(Source[HTMLPosition+2]) == 'W' && toupper(Source[HTMLPosition+3]) == '.' && toupper(Source[HTMLPosition+4]) != '.')
								CurrentPosition += 8;
						}
						else if (toupper(Source[HTMLPosition]) == 'W' && toupper(Source[HTMLPosition+1]) == 'W' && toupper(Source[HTMLPosition+2]) == 'W' && toupper(Source[HTMLPosition+3]) == '.' && toupper(Source[HTMLPosition+4]) != '.')
							CurrentPosition += 7;
					}
					else if (toupper(Source[CurrentPosition]) == 'H' && toupper(Source[CurrentPosition+1]) == 'T' && toupper(Source[CurrentPosition+2]) == 'T' && toupper(Source[CurrentPosition+3]) == 'P' && Source[CurrentPosition+4] == ':' && (Source[CurrentPosition+5] == '/' || Source[CurrentPosition+5] == '\\') && (Source[CurrentPosition+6] == '/' || Source[CurrentPosition+6] == '\\'))
					{
						HTMLPosition = CurrentPosition+7;
						if (toupper(Source[CurrentPosition+7]) == 'W' && toupper(Source[CurrentPosition+8]) == 'W' && toupper(Source[CurrentPosition+9]) == 'W' && toupper(Source[CurrentPosition+10]) == '.' && toupper(Source[CurrentPosition+11]) != '.')
							CurrentPosition += 7;
					}
					else if (toupper(Source[CurrentPosition]) == 'H' && toupper(Source[CurrentPosition+1]) == 'T' && toupper(Source[CurrentPosition+2]) == 'T' && toupper(Source[CurrentPosition+3]) == 'P' && toupper(Source[CurrentPosition+4]) == 'S' && Source[CurrentPosition+5] == ':' && (Source[CurrentPosition+6] == '/' || Source[CurrentPosition+6] == '\\') && (Source[CurrentPosition+7] == '/' || Source[CurrentPosition+7] == '\\'))
					{
						HTMLPosition = CurrentPosition+8;
						if (toupper(Source[CurrentPosition+8]) == 'W' && toupper(Source[CurrentPosition+9]) == 'W' && toupper(Source[CurrentPosition+10]) == 'W' && toupper(Source[CurrentPosition+11]) == '.' && toupper(Source[CurrentPosition+12]) != '.')
							CurrentPosition += 8;
					}
					else if (toupper(Source[CurrentPosition]) == 'W' && toupper(Source[CurrentPosition+1]) == 'W' && toupper(Source[CurrentPosition+2]) == 'W' && toupper(Source[CurrentPosition+3]) == '.' && toupper(Source[CurrentPosition+4]) != '.')
						HTMLPosition = CurrentPosition;
					if (HTMLPosition >= 0)
					{
						HTMLLinkLength[NumLinks] = 0;
						SpaceFound = FALSE;
						KeepLooking = TRUE;
						InsideBrackets = FALSE;
						while (NumLinks <= 1 && KeepLooking && HTMLLinkLength[NumLinks] < MAX_MESSAGE_BUFFER-1)
						{
							if (Source[HTMLPosition] == '\0' || Source[HTMLPosition] == 34 || Source[HTMLPosition] == '\'' || Source[HTMLPosition] == '\r' || Source[HTMLPosition] == '\n' || Source[HTMLPosition] == '\t' || Source[HTMLPosition] == '?' || Source[HTMLPosition] == '#' || Source[HTMLPosition] == '@' || Source[HTMLPosition] == '/' || Source[HTMLPosition] == '\\')
								KeepLooking = FALSE;
							else if (!InsideBrackets && (Source[HTMLPosition] == '[' || Source[HTMLPosition] == '{'))
								InsideBrackets = TRUE;
							else if (InsideBrackets && (Source[HTMLPosition] == ']' || Source[HTMLPosition] == '}'))
								InsideBrackets = FALSE;
							else if (InsideBrackets && (Source[HTMLPosition] == '[' || Source[HTMLPosition] == '{'))
								KeepLooking = FALSE;
							else if (!InsideBrackets && (Source[HTMLPosition] == ']' || Source[HTMLPosition] == '}'))
								KeepLooking = FALSE;
							else if (!InsideTag || !InsideQuotes)
								if (Source[HTMLPosition] == '|' || Source[HTMLPosition] == '!' || Source[HTMLPosition] == '^' || Source[HTMLPosition] == '%' || Source[HTMLPosition] == '$' || Source[HTMLPosition] == '*' || Source[HTMLPosition] == ':' || Source[HTMLPosition] == ';' || Source[HTMLPosition] == '<' || Source[HTMLPosition] == '>' || Source[HTMLPosition] == '(' || Source[HTMLPosition] == ')' || Source[HTMLPosition] == '~' || Source[HTMLPosition] == ',' || Source[HTMLPosition] == '=')
									KeepLooking = FALSE;
							if (SpaceFound && Source[HTMLPosition] != '@' && Source[HTMLPosition] != ' ')
								KeepLooking = FALSE;
							if (KeepLooking)
							{
								if (Source[HTMLPosition] == '&' && Source[HTMLPosition+1] != '#')
								{
									NumLinks++;
									HTMLPosition++;
									if (NumLinks <= 1)
										HTMLLinkLength[NumLinks] = 0;
									SpaceFound = FALSE;
								}
								else
								{
									if (Source[HTMLPosition] == ' ')
										SpaceFound = TRUE;
									if (HTMLLinkLength[NumLinks] > 0 || Source[HTMLPosition] != '.')
									{
										// Build HTML link but skip leading periods
										HTMLLink[NumLinks][HTMLLinkLength[NumLinks]] = Source[HTMLPosition];
										HTMLLinkLength[NumLinks]++;
									}
									HTMLPosition++;
									if (Source[HTMLPosition-1] == '@')
									{
										HTMLLinkLength[NumLinks] = 0;
										SpaceFound = FALSE;
									}
								}
							}
						}
						if (NumLinks <= 1)
							NumLinks++;
						for (Loop = 0; Loop < NumLinks; Loop++)
						{
							while (HTMLLink[Loop][HTMLLinkLength[Loop]-1] == ' ')
								HTMLLinkLength[Loop]--;
							HTMLLink[Loop][HTMLLinkLength[Loop]] = '\0';
						}
					}
					for (Loop = 0; Loop < NumLinks; Loop++)
						if (toupper(HTMLLink[Loop][0]) != 'M' || toupper(HTMLLink[Loop][1]) != 'A' || toupper(HTMLLink[Loop][2]) != 'I' || toupper(HTMLLink[Loop][3]) != 'L' || toupper(HTMLLink[Loop][4]) != 'T' || toupper(HTMLLink[Loop][5]) != 'O' || toupper(HTMLLink[Loop][6]) != ':')
						{
							// Remove any trailing periods from the link
							HTMLPosition = strlen(HTMLLink[Loop])-1;
							while (HTMLPosition >= 0 && HTMLLink[Loop][HTMLPosition] == '.')
							{
								HTMLLink[Loop][HTMLPosition] = '\0';
								HTMLPosition--;
							}
							#ifdef TESTING_LOG_RAW_HTML_LINKS
							UpdateLogFile(lpClientContext->AddressString,"Found raw link",HTMLLink[Loop]);
							#endif

							Count = 0;
							RunningCount = 0;
//							SearchAndReplace(HTMLLink[Loop],"..",".",&Count);
//							RunningCount += Count;
							Count = 0;
							SearchAndReplace(HTMLLink[Loop],"[DOT]",".",&Count);
							RunningCount += Count;
							Count = 0;
							SearchAndReplace(HTMLLink[Loop],"{DOT}",".",&Count);
							RunningCount += Count;
							if (MaxLinkSize > 0 && RunningCount > 0 && !lpClientContext->PermBlackList)
							{
								lpClientContext->WhiteList = FALSE;
								lpClientContext->PermBlackList = TRUE;
								lpClientContext->BlackListType = BL_FORMAT;
								lpClientContext->BlackListSubType = BL_SUB_FORMAT_BODY;
								lpClientContext->BlackListResult = FormatErrors;
								sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"Deceptive HTML link found");
							}
							else
							{
								Count = 0;
								if (strlen(HTMLLink[Loop]) > 0)
								{
									while (HTMLLink[Loop][strlen(HTMLLink[Loop])-1] == '.' || HTMLLink[Loop][strlen(HTMLLink[Loop])-1] == ' ')
										HTMLLink[Loop][strlen(HTMLLink[Loop])-1] = '\0';
									for (Loop2 = strlen(HTMLLink[Loop])-1; Loop2 >= 0; Loop2--)
										if (HTMLLink[Loop][Loop2] == '.')
											Count++;
								}
								if (Count <= 0 || HTMLLink[Loop][0] == '.' || strlen(HTMLLink[Loop]) < 4)
									HTMLLink[Loop][0] = '\0';
								if (MaxLinkSize > 0 && (int) strlen(HTMLLink[Loop]) > MaxLinkSize && !lpClientContext->WhiteList && !lpClientContext->PermBlackList)
								{
									lpClientContext->BlackListType = BL_FORMAT;
									lpClientContext->BlackListSubType = BL_SUB_FORMAT_BODY;
									lpClientContext->BlackListResult = FormatErrors;
									sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"HTML link size of %d characters found",(int) strlen(HTMLLink[Loop]));
								}
								else if (strlen(HTMLLink[Loop]) > 0)
								{
									#ifdef TESTING_DETAILED_LOGGING
									UpdateLogFile(lpClientContext->AddressString,"Found link",HTMLLink[Loop]);
									#endif
									_time64(&lpClientContext->LastAccess);

									// Only resolve the address if it's not a repeat of the last address resolved
									if (strlen(LastHTMLLink) <= 0 || _stricmp(LastHTMLLink,HTMLLink[Loop]) != 0)
									{
										lpClientContext->HTMLLinks++;
										strcpy_s(LastHTMLLink,sizeof(LastHTMLLink),HTMLLink[Loop]);
										if (AggressiveResolveAddress(lpClientContext,HTMLLink[Loop],h_addr_list))
										{
											// Compare HTML link with filter list
											_time64(&lpClientContext->LastAccess);
											Num1 = h_addr_list[0];
											Num2 = h_addr_list[1];
											Num3 = h_addr_list[2];
											Num4 = h_addr_list[3];
											sprintf_s(Buffer,sizeof(Buffer),"%s HTML resolved to [%d.%d.%d.%d]",HTMLLink[Loop],Num1,Num2,Num3,Num4);
											lpClientContext->HTMLLinksResolved++;
											if (lpClientContext->HTMLAddrCount < MAX_HTML_RECORDS)
											{
												AddrFound = FALSE;
												for (Loop2 = 0; !AddrFound && Loop2 < lpClientContext->HTMLAddrCount; Loop2++)
													if (lpClientContext->HTMLAddr[Loop2][0] == h_addr_list[0] && lpClientContext->HTMLAddr[Loop2][1] == h_addr_list[1] && lpClientContext->HTMLAddr[Loop2][2] == h_addr_list[2] && lpClientContext->HTMLAddr[Loop2][3] == h_addr_list[3])
														AddrFound = TRUE;
												if (!AddrFound)
												{
													lpClientContext->HTMLAddr[lpClientContext->HTMLAddrCount][0] = h_addr_list[0];
													lpClientContext->HTMLAddr[lpClientContext->HTMLAddrCount][1] = h_addr_list[1];
													lpClientContext->HTMLAddr[lpClientContext->HTMLAddrCount][2] = h_addr_list[2];
													lpClientContext->HTMLAddr[lpClientContext->HTMLAddrCount][3] = h_addr_list[3];
													lpClientContext->HTMLAddrCount++;
												}
											}
											#ifdef TESTING_DETAILED_LOGGING
											UpdateLogFile(lpClientContext->AddressString,"Forward Lookup of",Buffer);
											#endif
											EnterCriticalSection(&DomainCriticalSection);
											DomainAccessCount++;
											LeaveCriticalSection(&DomainCriticalSection);
											FilterList = DomainFilters;
											KeepLooking = TRUE;
											while (KeepLooking && !IPWhiteList && ContinueProcess(lpClientContext,TRUE) && FilterList != NULL)
											{
												// Check resolved HTML link against IP address
												if (FilterList->Filter[1] == '0' && !lpClientContext->PermBlackList)
												{
													if (IPInSubnet((unsigned char) FilterList->Filter[4],(unsigned char) FilterList->Filter[5],(unsigned char) FilterList->Filter[6],(unsigned char) FilterList->Filter[7],(unsigned char) FilterList->Filter[8],(unsigned char) FilterList->Filter[9],(unsigned char) FilterList->Filter[10],(unsigned char) FilterList->Filter[11],(unsigned char) h_addr_list[0],(unsigned char) h_addr_list[1],(unsigned char) h_addr_list[2],(unsigned char) h_addr_list[3]))
													{
														if (FilterList->Filter[0] == '0')
														{
															// Do not white list items for this case
															// But if found on white list then do not black list
															KeepLooking = FALSE;
														}
														else if (FilterList->Filter[0] == '3' || FilterList->Filter[0] == '4' || FilterList->Filter[0] == '5' || FilterList->Filter[0] == '6')
														{
															// Suspect IP ranges, suspect recipients, white list recipients and disregarded domains are not valid
														}
//														else if (lpClientContext->WhiteList || FilterList->Filter[0] == '2' || lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListType == BL_TAG || lpClientContext->BlackListType == BL_FORMAT || lpClientContext->BlackListResult == BL_RESULT_FORWARD)
														else if (FilterList->Filter[0] == '2' || (!lpClientContext->WhiteList && (lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListType == BL_TAG || lpClientContext->BlackListType == BL_FORMAT || lpClientContext->BlackListResult == BL_RESULT_FORWARD)))
														{
															// Only black list if IP is on permanent black list and sending IP is not white listed
															if (!lpClientContext->PermBlackList && !IPWhiteList)
															{
																if (FilterList->Filter[0] == '2')
																	lpClientContext->PermBlackList = TRUE;
																lpClientContext->WhiteList = FALSE;
																lpClientContext->BlackListType = BL_IP;
																lpClientContext->BlackListSubType = BL_SUB_IP_HTML;
																lpClientContext->BlackListResult = FilterList->Filter[2]-'0';
																if (FilterList->Filter[0] == '2' || !lpClientContext->WhiteList)
																{
																	Num1 = h_addr_list[0];
																	Num2 = h_addr_list[1];
																	Num3 = h_addr_list[2];
																	Num4 = h_addr_list[3];
																	sprintf_s(lpClientContext->FilteredBy,sizeof(lpClientContext->FilteredBy),"%s = [%d.%d.%d.%d] [HTML Forward Lookup]",HTMLLink,Num1,Num2,Num3,Num4);
																}
																if (lpClientContext->BlackListResult != BL_RESULT_TURFDIR && lpClientContext->BlackListResult != BL_RESULT_FORWARD && lpClientContext->BlackListResult != BL_RESULT_DELETE)
																	lpClientContext->BlackListResult = BL_RESULT_FORWARD;
															}
															KeepLooking = FALSE;
														}
													}
												}
												FilterList = (FILTER_ENTRY *) FilterList->pvNext;
											}
											EnterCriticalSection(&DomainCriticalSection);
											DomainAccessCount--;
											LeaveCriticalSection(&DomainCriticalSection);
										}
										else
											UpdateLogFile(lpClientContext->AddressString,"Could not resolve",HTMLLink[Loop]);
									}
								}
							}
						}
				}
				if (!InsideTag)
				{
					if (CurrentPosition != WritePosition)
					{
						Source[WritePosition] = Source[CurrentPosition];
						StringChanged = TRUE;
					}
					WritePosition++;
				}
			}
			CurrentPosition++;
		}
		if (StringChanged)
			Source[WritePosition] = '\0';
	}
	return(StringChanged);
}

BOOL SendToTurfDir(CLIENT_CONTEXT *lpClientContext,int BLType)
{
	DWORD			IoSize;
	int				Loop;
	__time64_t		CurrentTime;
	char			TextTime[256];
	BOOL			Result = FALSE,FileFailure = FALSE;

	if (strlen(lpClientContext->TurfFileName) > 0)
	{
		Result = TRUE;
		switch (BLType)
		{
			case BL_IP:			strcat_s(lpClientContext->TurfFileName,sizeof(lpClientContext->TurfFileName),".IP");
								break;
			case BL_DOMAIN:		strcat_s(lpClientContext->TurfFileName,sizeof(lpClientContext->TurfFileName),".Domain");
								break;
			case BL_KEYWORD:	strcat_s(lpClientContext->TurfFileName,sizeof(lpClientContext->TurfFileName),".Keyword");
								break;
			case BL_TAG:		strcat_s(lpClientContext->TurfFileName,sizeof(lpClientContext->TurfFileName),".Tag");
								break;
			case BL_FORMAT:		strcat_s(lpClientContext->TurfFileName,sizeof(lpClientContext->TurfFileName),".Format");
								break;
			default:			strcat_s(lpClientContext->TurfFileName,sizeof(lpClientContext->TurfFileName),".Unknown");
								break;
		}
		if (!lpClientContext->FileOpen && fopen_s(&lpClientContext->MessageFile,lpClientContext->FullFileName,"rb") == 0)
		{
			lpClientContext->FileOpen = TRUE;
			if (fopen_s(&lpClientContext->TurfFile,lpClientContext->TurfFileName,"wb") == 0)
			{
				lpClientContext->TurfFileOpen = TRUE;
				_time64(&CurrentTime);
				_ctime64_s(TextTime,sizeof(TextTime),&CurrentTime);
				SearchAndReplace(TextTime,"\n","\r\n",NULL);
				if (lpClientContext->TurfFileOpen)
				{
					if (fprintf(lpClientContext->TurfFile,"%s[%s]\r\n",TextTime,lpClientContext->AddressString) < 0)
						lpClientContext->TurfFileOpen = FALSE;
					else if (fprintf(lpClientContext->TurfFile,"Filtered by %s\r\n",lpClientContext->FilteredBy) < 0)
						lpClientContext->TurfFileOpen = FALSE;
					else if (fprintf(lpClientContext->TurfFile,"%s",lpClientContext->HELOcmd) < 0)
						lpClientContext->TurfFileOpen = FALSE;
					else if (fprintf(lpClientContext->TurfFile,"%s",lpClientContext->MAILcmd) < 0)
						lpClientContext->TurfFileOpen = FALSE;
					else if (fprintf(lpClientContext->TurfFile,"Subject: %s\r\n",lpClientContext->SubjectLine) < 0)
						lpClientContext->TurfFileOpen = FALSE;
					else if (fprintf(lpClientContext->TurfFile,"Process Time: %4.2f    Message Size: %ld\r\n",((float) lpClientContext->TimeSpan)/100,lpClientContext->MessageSize) < 0)
						lpClientContext->TurfFileOpen = FALSE;
				}
				for (Loop = 0; Result && lpClientContext->TurfFileOpen && Loop < lpClientContext->RCPTCount; Loop++)
					if (fprintf(lpClientContext->TurfFile,"%s",lpClientContext->RCPTcmd[Loop]) < 0)
						lpClientContext->TurfFileOpen = FALSE;
				if (lpClientContext->TurfFileOpen)
					if (fprintf(lpClientContext->TurfFile,"----------------------------\r\n") < 0)
						lpClientContext->TurfFileOpen = FALSE;
				while (!FileFailure && lpClientContext->FileOpen && lpClientContext->TurfFileOpen && !feof(lpClientContext->MessageFile))
				{
					IoSize = fread(lpClientContext->Buffer,sizeof(char),sizeof(lpClientContext->Buffer),lpClientContext->MessageFile);
					if ((long) IoSize > 0)
						fwrite(lpClientContext->Buffer,sizeof(char),(long) IoSize,lpClientContext->TurfFile);
					else if ((long) IoSize == 0)
					{
						// Do nothing
					}
					else
						FileFailure = TRUE;
				}
				fclose(lpClientContext->TurfFile);
				lpClientContext->TurfFileOpen = FALSE;
			}
			fclose(lpClientContext->MessageFile);
			lpClientContext->FileOpen = FALSE;
		}
		else
		{
			Result = FALSE;
			UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"SendToTurfDir() Failed to open file or file already open");
		}
		if (FileFailure)
			Result = FALSE;
	}
	return(Result);
}

BOOL ConnectToSmartHost(CLIENT_CONTEXT *lpClientContext,int RetryDelay)
{
	SOCKADDR_IN		addr;
	hostent FAR		*host;
	int				Num1,Num2,Num3,Num4,RetryCount = 10,RetryLoop;
	BOOL			Result = TRUE;

	if (lpClientContext != NULL)
	{
		if (isalpha(SmartHost[0]))
		{
			host = ::gethostbyname(SmartHost);
			if (host == NULL)
				Result = FALSE;
			else
			{
				addr.sin_addr.S_un.S_un_b.s_b1 = host->h_addr_list[0][0];
				addr.sin_addr.S_un.S_un_b.s_b2 = host->h_addr_list[0][1];
				addr.sin_addr.S_un.S_un_b.s_b3 = host->h_addr_list[0][2];
				addr.sin_addr.S_un.S_un_b.s_b4 = host->h_addr_list[0][3];
			}
		}
		else
		{
			Result = ConvertIPString(SmartHost,&Num1,&Num2,&Num3,&Num4);
			addr.sin_addr.S_un.S_un_b.s_b1 = Num1;
			addr.sin_addr.S_un.S_un_b.s_b2 = Num2;
			addr.sin_addr.S_un.S_un_b.s_b3 = Num3;
			addr.sin_addr.S_un.S_un_b.s_b4 = Num4;
		}
		if (!Result)
		{
			UpdateLogFile(SmartHost,lpClientContext->AddressString,"Invalid SmartHost address");
			strcpy_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"Action: failed");
		}
		_time64(&lpClientContext->LastAccess);
		YieldControl();
		if (Result)
		{
			addr.sin_family = AF_INET;
			addr.sin_port = ::htons(SmartHostPort);
			if ((lpClientContext->HostSocket = ::socket(AF_INET,SOCK_STREAM,0)) == INVALID_SOCKET)
			{
				UpdateLogFile(SmartHost,lpClientContext->AddressString,"Failed to create socket to SmartHost");
				Result = FALSE;
				strcpy_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"Action: failed");
			}
			if (Result)
			{
				Result = FALSE;
				while (!Result && RetryCount > 0)
				{
					if (::connect(lpClientContext->HostSocket,(LPSOCKADDR) &addr,sizeof(addr)) == SOCKET_ERROR)
					{
						RetryCount--;
						for (RetryLoop = 0; RetryLoop < 100; RetryLoop++)
						{
							Sleep(RetryDelay*10);
							_time64(&lpClientContext->LastAccess);
							YieldControl();
						}
					}
					else
						Result = TRUE;
					_time64(&lpClientContext->LastAccess);
					YieldControl();
				}
			}
			if (!Result)
			{
				UpdateLogFile(SmartHost,lpClientContext->AddressString,"Failed to connect to SmartHost");
				strcpy_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"Action: failed");
			}
		}
	}
	return(Result);
}

BOOL ForwardToSmartHost(CLIENT_CONTEXT *lpClientContext,BOOL BLForward,BOOL OnlyToWhiteRecipient)
{
	int				Loop,ReconnectCount = 10,RetryDelay = 500;
	DWORD			IoSize,IoLen;
	char			Buffer[MAX_KEYWORD_SIZE];
	BOOL			Result = TRUE,FileFailure = FALSE,WelcomeMessage = FALSE;

	#ifdef TESTING_PROCESS_LOGGING
	UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Starting ForwardToSmartHost()");
	#endif
	if (lpClientContext->MessageSize > 5)
	{
		lpClientContext->SendComplete = FALSE;
		Result = ConnectToSmartHost(lpClientContext,RetryDelay);
		if (Result)
		{
			lpClientContext->HostSocketOpen = TRUE;
			UpdateLogFile(SmartHost,lpClientContext->AddressString,"Connected to SmartHost");
			while (Result && !WelcomeMessage && ReconnectCount > 0)
			{
				// Wait for introduction
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"2 ",lpClientContext->AddressString);
				if (!Result)
				{
					::shutdown(lpClientContext->HostSocket,SD_BOTH);
					::closesocket(lpClientContext->HostSocket);
					lpClientContext->HostSocketOpen = FALSE;
					lpClientContext->HostSocket = INVALID_SOCKET;
					Sleep(RetryDelay*10);
					ReconnectCount--;
					if (ReconnectCount > 0)
						Result = ConnectToSmartHost(lpClientContext,RetryDelay);
				}
				else
					WelcomeMessage = TRUE;
			}
			if (!Result)
			{
				UpdateLogFile(SmartHost,lpClientContext->AddressString,"Failed to receive welcome message from SmartHost");
				if (strlen(lpClientContext->Buffer) > 0)
				{
					memset(Buffer,0,sizeof(Buffer));
					sprintf_s(Buffer,sizeof(Buffer)-1,"Received: %s",lpClientContext->Buffer);
					UpdateLogFile(SmartHost,lpClientContext->AddressString,Buffer);
				}
				strcpy_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"Action: failed");
			}
			else
			{
				// Send HELO
				sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"HELO SpamHater\r\n");
				UpdateLogFile(SmartHost,lpClientContext->AddressString,lpClientContext->Buffer);
				::send(lpClientContext->HostSocket,lpClientContext->Buffer,strlen(lpClientContext->Buffer),0);
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"25",lpClientContext->AddressString);
			}
			if (Result)
			{
				// Send MAIL FROM:
				UpdateLogFile(SmartHost,lpClientContext->AddressString,lpClientContext->MAILcmd);
				::send(lpClientContext->HostSocket,lpClientContext->MAILcmd,strlen(lpClientContext->MAILcmd),0);
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"25",lpClientContext->AddressString);
			}
			if (Result)
			{
				if (BLForward)
				{
					// Send RCTP TO: for black list forwarding address
					sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"RCPT TO:%s\r\n",ForwardingAddress);
					UpdateLogFile(SmartHost,lpClientContext->AddressString,lpClientContext->Buffer);
					::send(lpClientContext->HostSocket,lpClientContext->Buffer,strlen(lpClientContext->Buffer),0);
					Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"25",lpClientContext->AddressString);
				}
				else if (OnlyToWhiteRecipient && lpClientContext->WhiteRecipient >= 0 && lpClientContext->WhiteRecipient < lpClientContext->RCPTCount)
				{
					// Send RCTP TO:
					UpdateLogFile(SmartHost,lpClientContext->AddressString,lpClientContext->RCPTcmd[lpClientContext->WhiteRecipient]);
					::send(lpClientContext->HostSocket,lpClientContext->RCPTcmd[lpClientContext->WhiteRecipient],strlen(lpClientContext->RCPTcmd[lpClientContext->WhiteRecipient]),0);
					Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"25",lpClientContext->AddressString);
				}
				else
				{
					for (Loop = 0; Result && Loop < lpClientContext->RCPTCount; Loop++)
					{
						// Send RCTP TO:
						UpdateLogFile(SmartHost,lpClientContext->AddressString,lpClientContext->RCPTcmd[Loop]);
						::send(lpClientContext->HostSocket,lpClientContext->RCPTcmd[Loop],strlen(lpClientContext->RCPTcmd[Loop]),0);
						Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"25",lpClientContext->AddressString);
					}
				}
			}
			if (Result)
			{
				// Send DATA
				UpdateLogFile(SmartHost,lpClientContext->AddressString,"DATA");
				sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"DATA\r\n");
				::send(lpClientContext->HostSocket,lpClientContext->Buffer,strlen(lpClientContext->Buffer),0);
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"35",lpClientContext->AddressString);
			}
			if (Result)
			{
				// Send File
				if (!lpClientContext->FileOpen && fopen_s(&lpClientContext->MessageFile,lpClientContext->FullFileName,"rb") == 0)
				{
					lpClientContext->FileOpen = TRUE;
					if (strlen(lpClientContext->FilteredBy) > 0)
						sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"X-SpamHater: Filter=%s%s\r\n",(lpClientContext->WhiteList ? "White List " : ""),lpClientContext->FilteredBy);
					else
						sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"X-SpamHater: Filter=Unclassified message\r\n");
					::send(lpClientContext->HostSocket,lpClientContext->Buffer,strlen(lpClientContext->Buffer),0);
					sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"X-SpamHater: Steps='%s', %d Links found, %d Links resolved\r\n",lpClientContext->StepsTaken,lpClientContext->HTMLLinks,lpClientContext->HTMLLinksResolved);
					::send(lpClientContext->HostSocket,lpClientContext->Buffer,strlen(lpClientContext->Buffer),0);
					sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"X-SpamHater: Process Time=%4.2f    Message Size=%ld\r\n",((float) lpClientContext->TimeSpan)/100,lpClientContext->MessageSize);
					::send(lpClientContext->HostSocket,lpClientContext->Buffer,strlen(lpClientContext->Buffer),0);
					for (Loop = 0; Result && Loop < lpClientContext->RCPTCount; Loop++)
					{
						sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"X-SpamHater: %s",lpClientContext->RCPTcmd[Loop]);
						::send(lpClientContext->HostSocket,lpClientContext->Buffer,strlen(lpClientContext->Buffer),0);
					}
					while (!FileFailure && !feof(lpClientContext->MessageFile))
					{
						IoSize = fread(lpClientContext->Buffer,sizeof(char),sizeof(lpClientContext->Buffer)-5,lpClientContext->MessageFile);
						if ((long) IoSize > 0)
						{
							lpClientContext->Buffer[(long) IoSize] = '\0';
							if (lpClientContext->MessageTruncated || lpClientContext->MessageIncomplete)
							{
								strcpy_s(Buffer,sizeof(Buffer),lpClientContext->MessageID);
								if (strlen(Buffer) < MAX_KEYWORD_SIZE-5)
								{
									if (Buffer[strlen(Buffer)-1] == '>')
									{
										Buffer[strlen(Buffer)-1] = '\0';
										strcat_s(Buffer,sizeof(Buffer),"-inc>");
									}
									else
										strcat_s(Buffer,sizeof(Buffer),"-inc");
									if (FindString(lpClientContext->Buffer,lpClientContext->MessageID,SEARCH_CONTAINS))
									{
										SearchAndReplace(lpClientContext->Buffer,lpClientContext->MessageID,Buffer,NULL);
										IoSize += 4;
										IoLen = strlen(lpClientContext->Buffer);
										if ((long) IoLen > (long) IoSize)
											IoSize = (long) IoLen;
									}
								}
							}
							::send(lpClientContext->HostSocket,lpClientContext->Buffer,(long) IoSize,0);
							lpClientContext->Buffer[(long) IoSize] = '\0';
						}
						else
						{
							FileFailure = TRUE;
							strcpy_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"Action: failed");
						}
					}
					fclose(lpClientContext->MessageFile);
					lpClientContext->FileOpen = FALSE;
				}
				else
				{
					sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"\r\n.\r\n");
					::send(lpClientContext->HostSocket,lpClientContext->Buffer,strlen(lpClientContext->Buffer),0);
					FileFailure = TRUE;
					strcpy_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"Action: failed");
					UpdateLogFile(SmartHost,lpClientContext->AddressString,"ForwardToSmartHost() Failed to open file or file already open");
				}
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"25",lpClientContext->AddressString);
			}
			if (Result)
			{
				// Send QUIT
				UpdateLogFile(SmartHost,lpClientContext->AddressString,"QUIT");
				sprintf_s(lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"QUIT\r\n");
				::send(lpClientContext->HostSocket,lpClientContext->Buffer,strlen(lpClientContext->Buffer),0);
				ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,lpClientContext->Buffer,sizeof(lpClientContext->Buffer),"  ",lpClientContext->AddressString);
			}
			::shutdown(lpClientContext->HostSocket,SD_BOTH);
			::closesocket(lpClientContext->HostSocket);
			lpClientContext->HostSocketOpen = FALSE;
			lpClientContext->HostSocket = INVALID_SOCKET;
		}
		lpClientContext->SendComplete = TRUE;
		_time64(&lpClientContext->LastAccess);
	}
	if (FileFailure)
		Result = FALSE;
	if (!Result && (lpClientContext->WhiteList || lpClientContext->BlackListType == BL_NONE))
		Result = SendBounceMessage(lpClientContext,lpClientContext->Buffer);
	return(Result);
}

BOOL SendBounceMessage(CLIENT_CONTEXT *lpClientContext,char *ErrorReport)
{
	char			Buffer[MAX_MESSAGE_BUFFER],TimeString[MAX_WORK_BUFFER_SIZE];
	int				Loop,ReconnectCount = 10,RetryDelay = 500;
	BOOL			Result = TRUE,WelcomeMessage = FALSE;

	#ifdef TESTING_PROCESS_LOGGING
	UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Starting SendBounceMessage()");
	#endif
	if (strlen(ErrorReport) > 0 && strlen(lpClientContext->MAILAddress) > 0 && ValidAddress(lpClientContext->MAILAddress))
	{
		lpClientContext->SendComplete = FALSE;
		UpdateLogFile(SmartHost,lpClientContext->AddressString,"Sending Bounce Report");
		Result = ConnectToSmartHost(lpClientContext,RetryDelay);
		if (Result)
		{
			lpClientContext->HostSocketOpen = TRUE;
			UpdateLogFile(SmartHost,lpClientContext->AddressString,"Connected to SmartHost");
			while (Result && !WelcomeMessage && ReconnectCount > 0)
			{
				// Wait for introduction
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,Buffer,sizeof(Buffer),"2 ",lpClientContext->AddressString);
				if (!Result)
				{
					::shutdown(lpClientContext->HostSocket,SD_BOTH);
					::closesocket(lpClientContext->HostSocket);
					lpClientContext->HostSocketOpen = FALSE;
					lpClientContext->HostSocket = INVALID_SOCKET;
					Sleep(RetryDelay*10);
					ReconnectCount--;
					if (ReconnectCount > 0)
						Result = ConnectToSmartHost(lpClientContext,RetryDelay);
				}
				else
					WelcomeMessage = TRUE;
			}
			if (!Result)
			{
				UpdateLogFile(SmartHost,lpClientContext->AddressString,"Failed to receive welcome message from SmartHost");
				if (strlen(Buffer) > 0)
				{
					memset(TimeString,0,sizeof(TimeString));
					sprintf_s(TimeString,sizeof(TimeString)-1,"Received: %s",Buffer);
					UpdateLogFile(SmartHost,lpClientContext->AddressString,TimeString);
				}
			}
			else
			{
				// Send HELO
				sprintf_s(Buffer,sizeof(Buffer),"HELO SpamHater\r\n");
				UpdateLogFile(SmartHost,lpClientContext->AddressString,Buffer);
				::send(lpClientContext->HostSocket,Buffer,strlen(Buffer),0);
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,Buffer,sizeof(Buffer),"25",lpClientContext->AddressString);
			}
			if (Result)
			{
				// Send MAIL FROM:
				sprintf_s(Buffer,sizeof(Buffer),"MAIL FROM:%s\r\n",AdminAddress);
				UpdateLogFile(SmartHost,lpClientContext->AddressString,Buffer);
				::send(lpClientContext->HostSocket,Buffer,strlen(Buffer),0);
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,Buffer,sizeof(Buffer),"25",lpClientContext->AddressString);
			}
			if (Result)
			{
				// Send RCTP TO: for black list forwarding address
				sprintf_s(Buffer,sizeof(Buffer),"RCPT TO:%s\r\n",lpClientContext->MAILAddress);
				UpdateLogFile(SmartHost,lpClientContext->AddressString,Buffer);
				::send(lpClientContext->HostSocket,Buffer,strlen(Buffer),0);
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,Buffer,sizeof(Buffer),"25",lpClientContext->AddressString);
			}
			if (Result)
			{
				// Send DATA
				UpdateLogFile(SmartHost,lpClientContext->AddressString,"DATA");
				sprintf_s(Buffer,sizeof(Buffer),"DATA\r\n");
				::send(lpClientContext->HostSocket,Buffer,strlen(Buffer),0);
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,Buffer,sizeof(Buffer),"35",lpClientContext->AddressString);
			}
			if (Result)
			{
				// Send Bounce Report
				sprintf_s(Buffer,sizeof(Buffer),"Message-ID: <%04d-%s>\r\nDate: %s\r\nFrom: %s\r\nTo: %s\r\nSubject: Delivery Status Notification (Failure)\r\nMime-Version: 1.0\r\nContent-Type: text/plain; charset=\"ISO-8859-1\"\r\nContent-Transfer-Encoding: 7bit\r\n\r\nThis is an automatically generated Delivery Status Notification.\r\nSubject: %s\r\n\r\nDelivery to the following recipients failed.\r\n\r\n",lpClientContext->ConnectionID,AdminAddress,BuildDateString(TimeString,sizeof(TimeString)),AdminAddress,lpClientContext->MAILAddress,lpClientContext->SubjectLine);
				for (Loop = 0; Loop < lpClientContext->RCPTCount; Loop++)
					if (sizeof(Buffer)-strlen(Buffer) >= strlen(ErrorReport)+strlen(lpClientContext->RCPTAddress[Loop])+20)
					{
						strcat_s(Buffer,sizeof(Buffer),"       ");
						strcat_s(Buffer,sizeof(Buffer),lpClientContext->RCPTAddress[Loop]);
					}
				strcat_s(Buffer,sizeof(Buffer),"\r\n");
				strcat_s(Buffer,sizeof(Buffer),ErrorReport);
				strcat_s(Buffer,sizeof(Buffer),"\r\n.\r\n");
				::send(lpClientContext->HostSocket,Buffer,strlen(Buffer),0);
				Result = ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,Buffer,sizeof(Buffer),"25",lpClientContext->AddressString);
			}
			if (Result)
			{
				// Send QUIT
				UpdateLogFile(SmartHost,lpClientContext->AddressString,"QUIT");
				sprintf_s(Buffer,sizeof(Buffer),"QUIT\r\n");
				::send(lpClientContext->HostSocket,Buffer,strlen(Buffer),0);
				ReceiveSMTPResult(lpClientContext,lpClientContext->HostSocket,Buffer,sizeof(Buffer),"  ",lpClientContext->AddressString);
			}
			::shutdown(lpClientContext->HostSocket,SD_BOTH);
			::closesocket(lpClientContext->HostSocket);
			lpClientContext->HostSocketOpen = FALSE;
			lpClientContext->HostSocket = INVALID_SOCKET;
		}
		lpClientContext->SendComplete = TRUE;
		_time64(&lpClientContext->LastAccess);
	}
	return(Result);
}

BOOL ReceiveSMTPResult(CLIENT_CONTEXT *lpClientContext,SOCKET HostSocket,char *Buffer,int BufferSize,char *ExpectedResult,char *LogEvent)
{
	DWORD	IoSize,LastError = 0;
	char	ErrorBuffer[MAX_WORK_BUFFER_SIZE];
	BOOL	Result = TRUE;

	if (HostSocket != INVALID_SOCKET)
	{
		IoSize = ::recv(HostSocket,Buffer,BufferSize-1,0);
		_time64(&lpClientContext->LastAccess);
		while ((long) IoSize > 3 && isdigit(Buffer[0]) && isdigit(Buffer[1]) && isdigit(Buffer[2]) && Buffer[3] == '-')
		{
			Buffer[(long) IoSize] = '\0';
			UpdateLogFile(SmartHost,LogEvent,Buffer);
			IoSize = ::recv(HostSocket,Buffer,BufferSize-1,0);
		}
		if ((long) IoSize > 0 && isdigit(Buffer[0]) && isdigit(Buffer[1]) && isdigit(Buffer[2]) && Buffer[3] == ' ')
		{
			Buffer[(long) IoSize] = '\0';
			UpdateLogFile(SmartHost,LogEvent,Buffer);
			if ((ExpectedResult[0] != ' ' && Buffer[0] != ExpectedResult[0]) || (ExpectedResult[1] != ' ' && Buffer[1] != ExpectedResult[1]))
				Result = FALSE;
		}
		else
		{
			if (!lpClientContext->Timeout && !lpClientContext->TerminationMessage)
			{
				if (lpClientContext->LastError == 0)
				{
					lpClientContext->LastError = SocketError(lpClientContext);
					CheckSocketError(lpClientContext);
				}
				if (lpClientContext->LastError != WSAECONNRESET && lpClientContext->LastError != 0)
				{
					sprintf_s(ErrorBuffer,sizeof(ErrorBuffer),"Failed to receive data with WSA error %ld",(long) lpClientContext->LastError);
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),ErrorBuffer);
				}
				else
					UpdateLogFile(lpClientContext->AddressString,GetConnectionTag(lpClientContext),"Connection reset by client");
				CloseClient(lpClientContext,FALSE);
			}
			Result = FALSE;
			strcpy_s(Buffer,BufferSize,"Action: failed");
		}
	}
	else
	{
		Result = FALSE;
		strcpy_s(Buffer,BufferSize,"Action: failed");
	}
	return(Result);
}

BOOL ConvertIPString(char *String,int *Num1,int *Num2,int *Num3,int *Num4)
{
	char	*Position;
	int		Element;
	BOOL	Result = TRUE;

	*Num1 = 0;
	*Num2 = 0;
	*Num3 = 0;
	*Num4 = 0;
	Position = String;
	Element = 1;
	while (Result && *Position != '\0' && *Position != ' ' && *Position != '\r' && *Position != '\n')
	{
		if (*Position == '.')
		{
			Element++;
			if (Element > 4)
				Result = FALSE;
		}
		else if (isalpha(*Position))
			Result = FALSE;
		else
		{
			switch (Element)
			{
				case 1:	*Num1 *= 10;
						*Num1 += *Position-'0';
						break;
				case 2:	*Num2 *= 10;
						*Num2 += *Position-'0';
						break;
				case 3:	*Num3 *= 10;
						*Num3 += *Position-'0';
						break;
				case 4:	*Num4 *= 10;
						*Num4 += *Position-'0';
						break;
			}
		}
		Position++;
	}
	if (Element != 4 || *Num1 > 255 || *Num2 > 255 || *Num3 > 255 || *Num4 > 255)
		Result = FALSE;
	return(Result);
}

void UpdateLogFile(char *Address,char *Source,char *String)
{
	__time64_t	CurrentTime;
	char		TimeString[MAX_WORK_BUFFER_SIZE],LogEntry[MAX_WORK_BUFFER_SIZE*4],Buffer[MAX_WORK_BUFFER_SIZE];
	int			LinePosition,SourcePosition,AppendSize;

	#ifdef _DEBUG
	if (pThis != NULL)
		pThis->DebugMsg("%s %s %s","SMTP","Proxy","Entering UpdateLogFile()");
	#endif
	if (UpdateLog && SMTPLog != NULL)
	{
		EnterCriticalSection(&CommonFilesCriticalSection);
		_time64(&CurrentTime);
		_ctime64_s(TimeString,sizeof(TimeString),&CurrentTime);
		while (strlen(TimeString) > 0 && (TimeString[strlen(TimeString)-1] == '\r' || TimeString[strlen(TimeString)-1] == '\n'))
			TimeString[strlen(TimeString)-1] = '\0';
		TimeString[7] = '\0';
		TimeString[10] = '\0';
		TimeString[19] = '\0';
		sprintf_s(Buffer,sizeof(Buffer),"%s-%s-%s %s",&TimeString[20],&TimeString[4],&TimeString[8],&TimeString[11]);
		sprintf_s(LogEntry,sizeof(LogEntry),"%s %s",Buffer,Address);
		while (strlen(LogEntry) > 0 && (LogEntry[strlen(LogEntry)-1] == '\r' || LogEntry[strlen(LogEntry)-1] == '\n'))
			LogEntry[strlen(LogEntry)-1] = '\0';
		strcat_s(LogEntry,sizeof(LogEntry)," ");
		strcat_s(LogEntry,sizeof(LogEntry),Source);
		while (strlen(LogEntry) > 0 && (LogEntry[strlen(LogEntry)-1] == '\r' || LogEntry[strlen(LogEntry)-1] == '\n'))
			LogEntry[strlen(LogEntry)-1] = '\0';
		strcat_s(LogEntry,sizeof(LogEntry)," ");
		LinePosition = strlen(LogEntry);
		AppendSize = (MAX_WORK_BUFFER_SIZE*4)-LinePosition-3;
		SourcePosition = 0;
		while (SourcePosition < (int) strlen(String))
		{
			if (AppendSize > (int) strlen(&String[SourcePosition]))
				strcpy_s(&LogEntry[LinePosition],sizeof(LogEntry)-LinePosition-1,&String[SourcePosition]);
			else
			{
				strncpy_s(&LogEntry[LinePosition],sizeof(LogEntry)-LinePosition-1,&String[SourcePosition],AppendSize);
				LogEntry[LinePosition+AppendSize] = '\0';
			}
			SourcePosition += AppendSize;
			while (strlen(LogEntry) > 0 && (LogEntry[strlen(LogEntry)-1] == '\r' || LogEntry[strlen(LogEntry)-1] == '\n'))
				LogEntry[strlen(LogEntry)-1] = '\0';
			SearchAndReplace(LogEntry,"\r","~",NULL);
			SearchAndReplace(LogEntry,"\n","~",NULL);
			strcat_s(LogEntry,sizeof(LogEntry),"\n");
			if ((long) strlen(SMTPLog)+(long) strlen(LogEntry) >= (long) MAX_LOG_BUFFER-1)
				FlushLogBuffers();
			if (strlen(SMTPLog)+strlen(LogEntry) < MAX_LOG_BUFFER-1)
				strcat_s(SMTPLog,MAX_LOG_BUFFER,LogEntry);
		}
		LeaveCriticalSection(&CommonFilesCriticalSection);
		_time64(&CurrentTime);
		#ifdef TESTING_INSTANT_LOGGING
		FlushLogBuffers();
		#else
		if ((long) (CurrentTime-LastFlushTime) > 60 || (long) strlen(SMTPLog) > (long) MAX_LOG_BUFFER-MAX_LOG_BUFFER_THRESHOLD)
			FlushLogBuffers();
		#endif
		if ((long) (CurrentTime-LastConfigTime) > 20)
		{
			_time64(&LastConfigTime);
			LoadLocalDomainsFile();
			LoadDomainFilterFile();
			LoadKeywordFilterFile();
		}
	}
}

void FlushLogBuffers()
{
	FILE		*LogFile;
	int			StringLength;
	__time64_t	CurrentTime;
	char		LogFileName[MAX_PATH_SIZE],FullLogFileName[MAX_PATH_SIZE],TimeString[MAX_WORK_BUFFER_SIZE];

	if (DeleteLogDays > 0)
	{
		_time64(&CurrentTime);
		CurrentTime -= ((DWORD) DeleteLogDays)*24*60*60;
		_ctime64_s(TimeString,sizeof(TimeString),&CurrentTime);
		while (strlen(TimeString) > 0 && (TimeString[strlen(TimeString)-1] == '\r' || TimeString[strlen(TimeString)-1] == '\n'))
			TimeString[strlen(TimeString)-1] = '\0';
		TimeString[7] = '\0';
		TimeString[10] = '\0';
		sprintf_s(LogFileName,sizeof(LogFileName),"ex%s%s%s.log",&TimeString[22],&TimeString[4],&TimeString[8]);
		sprintf_s(FullLogFileName,sizeof(FullLogFileName),"%s%s",LogFilePath,LogFileName);
		if (_access(FullLogFileName,0) == 0)
			remove(FullLogFileName);
	}
	if (TrackingLogSize-LastSavedTrackingLogSize >= 20)
		SaveTrackingLogFile(NULL);
	if (SMTPLog != NULL && strlen(SMTPLog) > 0)
	{
		EnterCriticalSection(&CommonFilesCriticalSection);
		_time64(&CurrentTime);
		_ctime64_s(TimeString,sizeof(TimeString),&CurrentTime);
		while (strlen(TimeString) > 0 && (TimeString[strlen(TimeString)-1] == '\r' || TimeString[strlen(TimeString)-1] == '\n'))
			TimeString[strlen(TimeString)-1] = '\0';
		TimeString[7] = '\0';
		TimeString[10] = '\0';
		sprintf_s(LogFileName,sizeof(LogFileName),"ex%s%s%s.log",&TimeString[22],&TimeString[4],&TimeString[8]);
		sprintf_s(FullLogFileName,sizeof(FullLogFileName),"%s%s",LogFilePath,LogFileName);
		if (UpdateLog && SMTPLog != NULL)
			if ((StringLength = strlen(SMTPLog)) > 0)
				if (fopen_s(&LogFile,FullLogFileName,"at") == 0)
				{
					fprintf(LogFile,"%s",SMTPLog);
					fclose(LogFile);
					strcpy_s(SMTPLog,MAX_LOG_BUFFER,&SMTPLog[StringLength]);
				}
		LeaveCriticalSection(&CommonFilesCriticalSection);
	}
	_time64(&LastFlushTime);
}

void LoadLocalDomainsFile()
{
	HANDLE				FilePosition;
	WIN32_FIND_DATA		FileInfo;
	FILE				*TextFile;
	char				NewTextLine[MAX_WORK_BUFFER_SIZE],*Position;
	FILTER_ENTRY		*NewEntry;
	int					IPNum1,IPNum2,IPNum3,IPNum4,SubNum1,SubNum2,SubNum3,SubNum4;

	if (strlen(LocalDomains) > 0 && LocalAccessCount <= 0)
	{
		FilePosition = FindFirstFile(LocalDomains,&FileInfo);
		if (FilePosition != INVALID_HANDLE_VALUE)
			if ((FileInfo.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == 0 && (FileInfo.nFileSizeLow > 0 || FileInfo.nFileSizeHigh > 0))
				if (!LocalLoaded || LocalModified != FileInfo.ftLastWriteTime.dwLowDateTime)
				{
					EnterCriticalSection(&CommonFilesCriticalSection);
					if (fopen_s(&TextFile,LocalDomains,"rt") == 0)
					{
						LeaveCriticalSection(&CommonFilesCriticalSection);
						EnterCriticalSection(&LocalCriticalSection);
						if (LocalAccessCount <= 0)
						{
							UpdateLogFile("SMTP","Proxy","Loading Local domain list");
							LocalModified = FileInfo.ftLastWriteTime.dwLowDateTime;
							LocalLoaded = TRUE;
							EmptyLocalDomainsFile();
							while (fgets(NewTextLine,sizeof(NewTextLine)-1,TextFile) != NULL)
							{
								while (strlen(NewTextLine) > 0 && (NewTextLine[strlen(NewTextLine)-1] == '\r' || NewTextLine[strlen(NewTextLine)-1] == '\n'))
									NewTextLine[strlen(NewTextLine)-1] = '\0';
								if (strlen(NewTextLine) > 2 && NewTextLine[0] != '#' && NewTextLine[1] == ' ')
								{
									if (NewTextLine[0] == '0')
									{
										// IP Range
										Position = &NewTextLine[2];
										if (ConvertIPString(Position,&IPNum1,&IPNum2,&IPNum3,&IPNum4))
										{
											while (*Position != ' ' && *Position != '\0' && *Position != '\r' && *Position != '\n')
												Position++;
											if (*Position == ' ')
												Position++;
											if (ConvertIPString(Position,&SubNum1,&SubNum2,&SubNum3,&SubNum4))
											{
												#ifndef MEMORY_NEW_ALLOC
												NewEntry = new FILTER_ENTRY;
												#else
												NewEntry = (FILTER_ENTRY *) AllocateBlock(sizeof(FILTER_ENTRY),FALSE);
												#endif
												if (NewEntry != NULL)
												{
													memset(NewEntry,0,sizeof(FILTER_ENTRY));
													NewEntry->AllocSize = 11;
													#ifndef MEMORY_NEW_ALLOC
													NewEntry->Filter = new char[NewEntry->AllocSize];
													#else
													NewEntry->Filter = (char *) AllocateBlock(NewEntry->AllocSize,FALSE);
													#endif
													if (NewEntry->Filter != NULL)
													{
														memset(NewEntry->Filter,0,11);
														NewEntry->Filter[0] = NewTextLine[0];
														NewEntry->Filter[1] = NewTextLine[1];
														NewEntry->Filter[2] = IPNum1;
														NewEntry->Filter[3] = IPNum2;
														NewEntry->Filter[4] = IPNum3;
														NewEntry->Filter[5] = IPNum4;
														NewEntry->Filter[6] = SubNum1;
														NewEntry->Filter[7] = SubNum2;
														NewEntry->Filter[8] = SubNum3;
														NewEntry->Filter[9] = SubNum4;
														NewEntry->pvNext = NULL;
														if (LocalFilters != NULL)
															NewEntry->pvNext = LocalFilters;
														LocalFilters = NewEntry;
													}
													else
														#ifndef MEMORY_NEW_ALLOC
														delete NewEntry;
														#else
														ReleaseBlock((void *) NewEntry,sizeof(FILTER_ENTRY));
														#endif
												}
											}
										}
									}
									else if (NewTextLine[0] != '0')
									{
										// Domain
										#ifndef MEMORY_NEW_ALLOC
										NewEntry = new FILTER_ENTRY;
										#else
										NewEntry = (FILTER_ENTRY *) AllocateBlock(sizeof(FILTER_ENTRY),FALSE);
										#endif
										if (NewEntry != NULL)
										{
											memset(NewEntry,0,sizeof(FILTER_ENTRY));
											NewEntry->AllocSize = strlen(NewTextLine)+1;
											#ifndef MEMORY_NEW_ALLOC
											NewEntry->Filter = new char[NewEntry->AllocSize];
											#else
											NewEntry->Filter = (char *) AllocateBlock(NewEntry->AllocSize,FALSE);
											#endif
											if (NewEntry->Filter != NULL)
											{
												strcpy_s(NewEntry->Filter,strlen(NewTextLine)+1,NewTextLine);
												NewEntry->pvNext = NULL;
												if (LocalFilters != NULL)
													NewEntry->pvNext = LocalFilters;
												LocalFilters = NewEntry;
											}
											else
												#ifndef MEMORY_NEW_ALLOC
												delete NewEntry;
												#else
												ReleaseBlock((void *) NewEntry,sizeof(FILTER_ENTRY));
												#endif
										}
									}
								}
							}
						}
						fclose(TextFile);
						LeaveCriticalSection(&LocalCriticalSection);
						#ifdef TESTING_PROCESS_LOGGING
						UpdateLogFile("SMTP","Proxy","Load Local domain list complete");
						#endif
					}
					else
						LeaveCriticalSection(&CommonFilesCriticalSection);
				}
	}
}

void EmptyLocalDomainsFile()
{
	FILTER_ENTRY	*CurrentEntry;

	if (LocalFilters != NULL && LocalAccessCount <= 0)
	{
		#ifdef TESTING_PROCESS_LOGGING
		UpdateLogFile("SMTP","Proxy","Clearing Local domain list");
		#endif
		while (LocalFilters != NULL)
		{
			CurrentEntry = LocalFilters;
			LocalFilters = (FILTER_ENTRY *) LocalFilters->pvNext;
			if (CurrentEntry->Filter != NULL)
				#ifndef MEMORY_NEW_ALLOC
				delete [] CurrentEntry->Filter;
				#else
				ReleaseBlock((void *) CurrentEntry->Filter,CurrentEntry->AllocSize);
				#endif
			#ifndef MEMORY_NEW_ALLOC
			delete CurrentEntry;
			#else
			ReleaseBlock((void *) CurrentEntry,sizeof(FILTER_ENTRY));
			#endif
		}
	}
}

void LoadDomainFilterFile()
{
	HANDLE				FilePosition;
	WIN32_FIND_DATA		FileInfo;
	FILE				*TextFile;
	char				NewTextLine[MAX_WORK_BUFFER_SIZE],*Position;
	FILTER_ENTRY		*NewEntry;
	int					IPNum1,IPNum2,IPNum3,IPNum4,SubNum1,SubNum2,SubNum3,SubNum4;

	if (strlen(DomainList) > 0 && DomainAccessCount <= 0)
	{
		FilePosition = FindFirstFile(DomainList,&FileInfo);
		if (FilePosition != INVALID_HANDLE_VALUE)
			if ((FileInfo.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == 0 && (FileInfo.nFileSizeLow > 0 || FileInfo.nFileSizeHigh > 0))
				if (!DomainLoaded || DomainModified != FileInfo.ftLastWriteTime.dwLowDateTime)
				{
					EnterCriticalSection(&CommonFilesCriticalSection);
					if (fopen_s(&TextFile,DomainList,"rt") == 0)
					{
						LeaveCriticalSection(&CommonFilesCriticalSection);
						EnterCriticalSection(&DomainCriticalSection);
						if (DomainAccessCount <= 0)
						{
							UpdateLogFile("SMTP","Proxy","Loading Domain filter list");
							DomainModified = FileInfo.ftLastWriteTime.dwLowDateTime;
							DomainLoaded = TRUE;
							EmptyDomainFilterFile();
							while (fgets(NewTextLine,sizeof(NewTextLine)-1,TextFile) != NULL)
							{
								while (strlen(NewTextLine) > 0 && (NewTextLine[strlen(NewTextLine)-1] == '\r' || NewTextLine[strlen(NewTextLine)-1] == '\n'))
									NewTextLine[strlen(NewTextLine)-1] = '\0';
								if (strlen(NewTextLine) > 4 && NewTextLine[0] != '#' && NewTextLine[3] == ' ')
								{
									if (NewTextLine[1] == '0')
									{
										// IP Range
										Position = &NewTextLine[4];
										if (ConvertIPString(Position,&IPNum1,&IPNum2,&IPNum3,&IPNum4))
										{
											while (*Position != ' ' && *Position != '\0' && *Position != '\r' && *Position != '\n')
												Position++;
											if (*Position == ' ')
												Position++;
											if (ConvertIPString(Position,&SubNum1,&SubNum2,&SubNum3,&SubNum4))
											{
												#ifndef MEMORY_NEW_ALLOC
												NewEntry = new FILTER_ENTRY;
												#else
												NewEntry = (FILTER_ENTRY *) AllocateBlock(sizeof(FILTER_ENTRY),FALSE);
												#endif
												if (NewEntry != NULL)
												{
													memset(NewEntry,0,sizeof(FILTER_ENTRY));
													NewEntry->AllocSize = 13;
													#ifndef MEMORY_NEW_ALLOC
													NewEntry->Filter = new char[NewEntry->AllocSize];
													#else
													NewEntry->Filter = (char *) AllocateBlock(NewEntry->AllocSize,FALSE);
													#endif
													if (NewEntry->Filter != NULL)
													{
														memset(NewEntry->Filter,0,11);
														NewEntry->Filter[0] = NewTextLine[0];
														NewEntry->Filter[1] = NewTextLine[1];
														NewEntry->Filter[2] = NewTextLine[2];
														NewEntry->Filter[3] = NewTextLine[3];
														NewEntry->Filter[4] = IPNum1;
														NewEntry->Filter[5] = IPNum2;
														NewEntry->Filter[6] = IPNum3;
														NewEntry->Filter[7] = IPNum4;
														NewEntry->Filter[8] = SubNum1;
														NewEntry->Filter[9] = SubNum2;
														NewEntry->Filter[10] = SubNum3;
														NewEntry->Filter[11] = SubNum4;
														NewEntry->pvNext = NULL;
														if (DomainFilters != NULL)
															NewEntry->pvNext = DomainFilters;
														DomainFilters = NewEntry;
													}
													else
														#ifndef MEMORY_NEW_ALLOC
														delete NewEntry;
														#else
														ReleaseBlock((void *) NewEntry,sizeof(FILTER_ENTRY));
														#endif
												}
											}
										}
									}
									else if (NewTextLine[1] != '0')
									{
										// Domain
										#ifndef MEMORY_NEW_ALLOC
										NewEntry = new FILTER_ENTRY;
										#else
										NewEntry = (FILTER_ENTRY *) AllocateBlock(sizeof(FILTER_ENTRY),FALSE);
										#endif
										if (NewEntry != NULL)
										{
											memset(NewEntry,0,sizeof(FILTER_ENTRY));
											NewEntry->AllocSize = strlen(NewTextLine)+1;
											#ifndef MEMORY_NEW_ALLOC
											NewEntry->Filter = new char[NewEntry->AllocSize];
											#else
											NewEntry->Filter = (char *) AllocateBlock(NewEntry->AllocSize,FALSE);
											#endif
											if (NewEntry->Filter != NULL)
											{
												strcpy_s(NewEntry->Filter,strlen(NewTextLine)+1,NewTextLine);
												NewEntry->pvNext = NULL;
												if (DomainFilters != NULL)
													NewEntry->pvNext = DomainFilters;
												DomainFilters = NewEntry;
											}
											else
												#ifndef MEMORY_NEW_ALLOC
												delete NewEntry;
												#else
												ReleaseBlock((void *) NewEntry,sizeof(FILTER_ENTRY));
												#endif
										}
									}
								}
							}
						}
						fclose(TextFile);
						LeaveCriticalSection(&DomainCriticalSection);
						#ifdef TESTING_PROCESS_LOGGING
						UpdateLogFile("SMTP","Proxy","Load Domain filter list complete");
						#endif
					}
					else
						LeaveCriticalSection(&CommonFilesCriticalSection);
				}
	}
}

void EmptyDomainFilterFile()
{
	FILTER_ENTRY	*CurrentEntry;

	if (DomainFilters != NULL && DomainAccessCount <= 0)
	{
		#ifdef TESTING_PROCESS_LOGGING
		UpdateLogFile("SMTP","Proxy","Clearing Domain filter list");
		#endif
		while (DomainFilters != NULL)
		{
			CurrentEntry = DomainFilters;
			DomainFilters = (FILTER_ENTRY *) DomainFilters->pvNext;
			if (CurrentEntry->Filter != NULL)
				#ifndef MEMORY_NEW_ALLOC
				delete [] CurrentEntry->Filter;
				#else
				ReleaseBlock((void *) CurrentEntry->Filter,CurrentEntry->AllocSize);
				#endif
			#ifndef MEMORY_NEW_ALLOC
			delete CurrentEntry;
			#else
			ReleaseBlock((void *) CurrentEntry,sizeof(FILTER_ENTRY));
			#endif
		}
	}
}

void LoadKeywordFilterFile()
{
	HANDLE				FilePosition;
	WIN32_FIND_DATA		FileInfo;
	FILE				*TextFile;
	char				NewTextLine[MAX_WORK_BUFFER_SIZE];
	FILTER_ENTRY		*NewEntry;

	if (strlen(KeywordList) > 0 && KeywordAccessCount <= 0)
	{
		FilePosition = FindFirstFile(KeywordList,&FileInfo);
		if (FilePosition != INVALID_HANDLE_VALUE)
			if ((FileInfo.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == 0 && (FileInfo.nFileSizeLow > 0 || FileInfo.nFileSizeHigh > 0))
				if (!KeywordLoaded || KeywordModified != FileInfo.ftLastWriteTime.dwLowDateTime)
				{
					EnterCriticalSection(&CommonFilesCriticalSection);
					if (fopen_s(&TextFile,KeywordList,"rt") == 0)
					{
						LeaveCriticalSection(&CommonFilesCriticalSection);
						EnterCriticalSection(&KeywordCriticalSection);
						if (KeywordAccessCount <= 0)
						{
							UpdateLogFile("SMTP","Proxy","Loading Keyword filter list");
							KeywordModified = FileInfo.ftLastWriteTime.dwLowDateTime;
							KeywordLoaded = TRUE;
							EmptyKeywordFilterFile();
							while (fgets(NewTextLine,sizeof(NewTextLine)-1,TextFile) != NULL)
							{
								while (strlen(NewTextLine) > 0 && (NewTextLine[strlen(NewTextLine)-1] == '\r' || NewTextLine[strlen(NewTextLine)-1] == '\n'))
									NewTextLine[strlen(NewTextLine)-1] = '\0';
								if (strlen(NewTextLine) >= 6 && NewTextLine[0] != '#' && NewTextLine[5] == ' ')
								{
									#ifndef MEMORY_NEW_ALLOC
									NewEntry = new FILTER_ENTRY;
									#else
									NewEntry = (FILTER_ENTRY *) AllocateBlock(sizeof(FILTER_ENTRY),FALSE);
									#endif
									if (NewEntry != NULL)
									{
										memset(NewEntry,0,sizeof(FILTER_ENTRY));
										NewEntry->AllocSize = strlen(NewTextLine)+1;
										#ifndef MEMORY_NEW_ALLOC
										NewEntry->Filter = new char[NewEntry->AllocSize];
										#else
										NewEntry->Filter = (char *) AllocateBlock(NewEntry->AllocSize,FALSE);
										#endif
										if (NewEntry->Filter != NULL)
										{
											strcpy_s(NewEntry->Filter,strlen(NewTextLine)+1,NewTextLine);
											NewEntry->pvNext = NULL;
											if (KeywordFilters != NULL)
												NewEntry->pvNext = KeywordFilters;
											KeywordFilters = NewEntry;
										}
										else
											#ifndef MEMORY_NEW_ALLOC
											delete NewEntry;
											#else
											ReleaseBlock((void *) NewEntry,sizeof(FILTER_ENTRY));
											#endif
									}
								}
							}
						}
						fclose(TextFile);
						LeaveCriticalSection(&KeywordCriticalSection);
						#ifdef TESTING_PROCESS_LOGGING
						UpdateLogFile("SMTP","Proxy","Load Keyword filter list complete");
						#endif
					}
					else
						LeaveCriticalSection(&CommonFilesCriticalSection);
				}
	}
}

void EmptyKeywordFilterFile()
{
	FILTER_ENTRY	*CurrentEntry;

	if (KeywordFilters != NULL)
	{
		#ifdef TESTING_PROCESS_LOGGING
		UpdateLogFile("SMTP","Proxy","Clearing Keyword filter list");
		#endif
		while (KeywordFilters != NULL)
		{
			CurrentEntry = KeywordFilters;
			KeywordFilters = (FILTER_ENTRY *) KeywordFilters->pvNext;
			if (CurrentEntry->Filter != NULL)
				#ifndef MEMORY_NEW_ALLOC
				delete [] CurrentEntry->Filter;
				#else
				ReleaseBlock((void *) CurrentEntry->Filter,CurrentEntry->AllocSize);
				#endif
			#ifndef MEMORY_NEW_ALLOC
			delete CurrentEntry;
			#else
			ReleaseBlock((void *) CurrentEntry,sizeof(FILTER_ENTRY));
			#endif
		}
	}
}

void SortOutbreakFile(CLIENT_CONTEXT *lpClientContext)
{
	FILTER_ENTRY	*CurrentEntry,*CompareEntry,*PreviousEntry1,*PreviousEntry2,*SwapEntry;
	BOOL			PerformSwap;

	if (strlen(TrackingLogFile) > 0 && TrackingLog != NULL)
	{
		#ifdef TESTING_PROCESS_LOGGING
		UpdateLogFile("SMTP","Proxy","Sorting outbreak list");
		#endif
		EnterCriticalSection(&OutbreakCriticalSection);
		PreviousEntry1 = NULL;
		PreviousEntry2 = NULL;
		CurrentEntry = OutbreakFilters;
		if (CurrentEntry != NULL)
		{
			PreviousEntry2 = CurrentEntry;
			CompareEntry = (FILTER_ENTRY *) CurrentEntry->pvNext;
		}
		else
			CompareEntry = NULL;
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Outbreak List","Start sort");
		#endif
		while (CurrentEntry != NULL && CompareEntry != NULL)
		{
			while (CompareEntry != NULL)
			{
				if (lpClientContext != NULL)
					_time64(&lpClientContext->LastAccess);
				PerformSwap = FALSE;
				if ((unsigned char) CurrentEntry->Filter[4] > (unsigned char) CompareEntry->Filter[4])
					PerformSwap = TRUE;
				else if ((unsigned char) CurrentEntry->Filter[4] == (unsigned char) CompareEntry->Filter[4])
				{
					if ((unsigned char) CurrentEntry->Filter[5] > (unsigned char) CompareEntry->Filter[5])
						PerformSwap = TRUE;
					else if ((unsigned char) CurrentEntry->Filter[5] == (unsigned char) CompareEntry->Filter[5])
					{
						if ((unsigned char) CurrentEntry->Filter[6] > (unsigned char) CompareEntry->Filter[6])
							PerformSwap = TRUE;
						else if ((unsigned char) CurrentEntry->Filter[6] == (unsigned char) CompareEntry->Filter[6])
						{
							if ((unsigned char) CurrentEntry->Filter[7] > (unsigned char) CompareEntry->Filter[7])
								PerformSwap = TRUE;
						}
					}
				}
				if (PerformSwap)
				{
					if (PreviousEntry1 != NULL)
						PreviousEntry1->pvNext = CompareEntry;
					SwapEntry = (FILTER_ENTRY *) CompareEntry->pvNext;
					if (CurrentEntry->pvNext != CompareEntry)
						CompareEntry->pvNext = CurrentEntry->pvNext;
					else
						CompareEntry->pvNext = CurrentEntry;
					CurrentEntry->pvNext = SwapEntry;
					if (CompareEntry->pvNext != CurrentEntry)
					{
						if (PreviousEntry2 != NULL)
							PreviousEntry2->pvNext = CurrentEntry;
					}
					else
						PreviousEntry2 = CompareEntry;
					SwapEntry = CompareEntry;
					CompareEntry = CurrentEntry;
					CurrentEntry = SwapEntry;
					if (OutbreakFilters == CompareEntry)
						OutbreakFilters = CurrentEntry;
				}
				PreviousEntry2 = CompareEntry;
				CompareEntry = (FILTER_ENTRY *) CompareEntry->pvNext;
			}
			PreviousEntry1 = CurrentEntry;
			CurrentEntry = (FILTER_ENTRY *) CurrentEntry->pvNext;
			if (CurrentEntry != NULL)
			{
				PreviousEntry2 = CurrentEntry;
				CompareEntry = (FILTER_ENTRY *) CurrentEntry->pvNext;
			}
			else
			{
				PreviousEntry2 = NULL;
				CompareEntry = NULL;
			}
		}
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Outbreak List","Stop sort");
		#endif
		LeaveCriticalSection(&OutbreakCriticalSection);
	}
}

void EmptyOutbreakFile()
{
	FILTER_ENTRY	*CurrentEntry;

	if (OutbreakFilters != NULL)
	{
		#ifdef TESTING_PROCESS_LOGGING
		UpdateLogFile("SMTP","Proxy","Clearing outbreak list");
		#endif
		while (OutbreakFilters != NULL)
		{
			CurrentEntry = OutbreakFilters;
			OutbreakFilters = (FILTER_ENTRY *) OutbreakFilters->pvNext;
			if (CurrentEntry->Filter != NULL)
				#ifndef MEMORY_NEW_ALLOC
				delete [] CurrentEntry->Filter;
				#else
				ReleaseBlock((void *) CurrentEntry->Filter,CurrentEntry->AllocSize);
				#endif
			#ifndef MEMORY_NEW_ALLOC
			delete CurrentEntry;
			#else
			ReleaseBlock((void *) CurrentEntry,sizeof(FILTER_ENTRY));
			#endif
		}
	}
	OutbreakLogSize = 0;
}

void LoadTrackingLogFile(CLIENT_CONTEXT *lpClientContext)
{
	FILE				*TextFile;
	char				NewTextLine[MAX_WORK_BUFFER_SIZE];
	int					OutbreakIP1,OutbreakIP2,OutbreakIP3,OutbreakIP4;
	FILTER_ENTRY		*NewEntry;
	CLIENT_CONTEXT		*NewContext;

	if (strlen(TrackingLogFile) > 0)
	{
		#ifndef MEMORY_NEW_ALLOC
		NewContext = new CLIENT_CONTEXT;
		#else
		NewContext = (CLIENT_CONTEXT *) AllocateBlock(sizeof(CLIENT_CONTEXT),TRUE);
		#endif
		EnterCriticalSection(&CommonFilesCriticalSection);
		if (fopen_s(&TextFile,TrackingLogFile,"rt") == 0)
		{
			LeaveCriticalSection(&CommonFilesCriticalSection);
			UpdateLogFile("SMTP","Proxy","Loading tracking log");
			EnterCriticalSection(&TrackingCriticalSection);
			EmptyTrackingLogFile();
			while (fgets(NewTextLine,sizeof(NewTextLine)-1,TextFile) != NULL)
			{
				if (lpClientContext != NULL)
					_time64(&lpClientContext->LastAccess);
				while (strlen(NewTextLine) > 0 && (NewTextLine[strlen(NewTextLine)-1] == '\r' || NewTextLine[strlen(NewTextLine)-1] == '\n'))
					NewTextLine[strlen(NewTextLine)-1] = '\0';
				if (strlen(NewTextLine) >= 6 && NewTextLine[0] != '#' && NewTextLine[5] == ' ')
				{
					#ifndef MEMORY_NEW_ALLOC
					NewEntry = new FILTER_ENTRY;
					#else
					NewEntry = (FILTER_ENTRY *) AllocateBlock(sizeof(FILTER_ENTRY),FALSE);
					#endif
					if (NewEntry != NULL)
					{
						memset(NewEntry,0,sizeof(FILTER_ENTRY));
						NewEntry->AllocSize = strlen(NewTextLine)+1;
						#ifndef MEMORY_NEW_ALLOC
						NewEntry->Filter = new char[NewEntry->AllocSize];
						#else
						NewEntry->Filter = (char *) AllocateBlock(NewEntry->AllocSize,FALSE);
						#endif
						if (NewEntry->Filter != NULL)
						{
							strcpy_s(NewEntry->Filter,strlen(NewTextLine)+1,NewTextLine);
							NewEntry->pvNext = NULL;
							if (TrackingLog != NULL)
								NewEntry->pvNext = TrackingLog;
							TrackingLog = NewEntry;
							TrackingLogSize++;
							LastSavedTrackingLogSize++;
						}
						else
							#ifndef MEMORY_NEW_ALLOC
							delete NewEntry;
							#else
							ReleaseBlock((void *) NewEntry,sizeof(FILTER_ENTRY));
							#endif
					}
				}
				else if (OutbreakCheck && NewContext != NULL && strlen(NewTextLine) > 20 && NewTextLine[0] == '#' && NewTextLine[1] == ' ' && NewTextLine[2] == '2' && NewTextLine[3] == '0' && NewTextLine[5] == ' ')
				{
					// Load Outbreak IP
					if (ConvertIPString(&NewTextLine[6],&OutbreakIP1,&OutbreakIP2,&OutbreakIP3,&OutbreakIP4))
					{
						NewContext->ConnectionAddress.sa_data[2] = (unsigned char) OutbreakIP1;
						NewContext->ConnectionAddress.sa_data[3] = (unsigned char) OutbreakIP2;
						NewContext->ConnectionAddress.sa_data[4] = (unsigned char) OutbreakIP3;
						NewContext->ConnectionAddress.sa_data[5] = (unsigned char) OutbreakIP4;
						RecordOutbreakTracking(NewContext,NewTextLine[4]);
					}
				}
			}
			LeaveCriticalSection(&TrackingCriticalSection);
			fclose(TextFile);
			#ifdef TESTING_PROCESS_LOGGING
			UpdateLogFile("SMTP","Proxy","Load tracking log complete");
			#endif
		}
		else
			LeaveCriticalSection(&CommonFilesCriticalSection);
		if (NewContext != NULL)
			#ifndef MEMORY_NEW_ALLOC
			delete NewContext;
			#else
			ReleaseBlock((void *) NewContext,sizeof(CLIENT_CONTEXT));
			#endif
	}
}

void SaveTrackingLogFile(CLIENT_CONTEXT *lpClientContext)
{
	int				Num1,Num2,Num3,Num4,Num5,Num6,Num7,Num8;
	FILE			*TextFile;
	FILTER_ENTRY	*CurrentEntry;

	LastSavedTrackingLogSize = TrackingLogSize;
	if (strlen(TrackingLogFile) > 0 && TrackingLog != NULL)
	{
		SortTrackingLogFile(lpClientContext);
		SortOutbreakFile(lpClientContext);
		EnterCriticalSection(&CommonFilesCriticalSection);
		if (fopen_s(&TextFile,TrackingLogFile,"wt") == 0)
		{
			LeaveCriticalSection(&CommonFilesCriticalSection);
			UpdateLogFile("SMTP","Proxy","Saving tracking log");

			EnterCriticalSection(&OutbreakCriticalSection);
			fprintf(TextFile,"# Outbreak Information\n");
			fprintf(TextFile,"#\n");
			CurrentEntry = OutbreakFilters;
			while (CurrentEntry != NULL)
			{
				if (lpClientContext != NULL)
					_time64(&lpClientContext->LastAccess);
				if (CurrentEntry->Filter != NULL)
				{
					Num1 = (unsigned char) CurrentEntry->Filter[4];
					Num2 = (unsigned char) CurrentEntry->Filter[5];
					Num3 = (unsigned char) CurrentEntry->Filter[6];
					Num4 = (unsigned char) CurrentEntry->Filter[7];
					Num5 = (unsigned char) CurrentEntry->Filter[8];
					Num6 = (unsigned char) CurrentEntry->Filter[9];
					Num7 = (unsigned char) CurrentEntry->Filter[10];
					Num8 = (unsigned char) CurrentEntry->Filter[11];
					fprintf(TextFile,"# %c%c%c %d.%d.%d.%d %d.%d.%d.%d\n",CurrentEntry->Filter[0],CurrentEntry->Filter[1],CurrentEntry->Filter[2],Num1,Num2,Num3,Num4,Num5,Num6,Num7,Num8);
				}
				CurrentEntry = (FILTER_ENTRY *) CurrentEntry->pvNext;
			}
			LeaveCriticalSection(&OutbreakCriticalSection);

			EnterCriticalSection(&TrackingCriticalSection);
			fprintf(TextFile,"#\n");
			fprintf(TextFile,"# Tracking Information\n");
			fprintf(TextFile,"#\n");
			CurrentEntry = TrackingLog;
			while (CurrentEntry != NULL)
			{
				if (lpClientContext != NULL)
					_time64(&lpClientContext->LastAccess);
				if (CurrentEntry->Filter != NULL)
					fprintf(TextFile,"%s\n",CurrentEntry->Filter);
				CurrentEntry = (FILTER_ENTRY *) CurrentEntry->pvNext;
			}
			LeaveCriticalSection(&TrackingCriticalSection);
			fclose(TextFile);
		}
		else
			LeaveCriticalSection(&CommonFilesCriticalSection);
	}
}

void SortTrackingLogFile(CLIENT_CONTEXT *lpClientContext)
{
	FILTER_ENTRY	*CurrentEntry,*CompareEntry,*PreviousEntry1,*PreviousEntry2,*SwapEntry;

	if (strlen(TrackingLogFile) > 0 && TrackingLog != NULL)
	{
		#ifdef TESTING_PROCESS_LOGGING
		UpdateLogFile("SMTP","Proxy","Sorting tracking log");
		#endif
		EnterCriticalSection(&TrackingCriticalSection);
		PreviousEntry1 = NULL;
		PreviousEntry2 = NULL;
		CurrentEntry = TrackingLog;
		if (CurrentEntry != NULL)
		{
			PreviousEntry2 = CurrentEntry;
			CompareEntry = (FILTER_ENTRY *) CurrentEntry->pvNext;
		}
		else
			CompareEntry = NULL;
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Tracking Log","Start sort");
		#endif
		while (CurrentEntry != NULL && CompareEntry != NULL)
		{
			while (CompareEntry != NULL)
			{
				if (lpClientContext != NULL)
					_time64(&lpClientContext->LastAccess);
				if (_stricmp(CurrentEntry->Filter,CompareEntry->Filter) < 0)
				{
					if (PreviousEntry1 != NULL)
						PreviousEntry1->pvNext = CompareEntry;
					SwapEntry = (FILTER_ENTRY *) CompareEntry->pvNext;
					if (CurrentEntry->pvNext != CompareEntry)
						CompareEntry->pvNext = CurrentEntry->pvNext;
					else
						CompareEntry->pvNext = CurrentEntry;
					CurrentEntry->pvNext = SwapEntry;
					if (CompareEntry->pvNext != CurrentEntry)
					{
						if (PreviousEntry2 != NULL)
							PreviousEntry2->pvNext = CurrentEntry;
					}
					else
						PreviousEntry2 = CompareEntry;
					SwapEntry = CompareEntry;
					CompareEntry = CurrentEntry;
					CurrentEntry = SwapEntry;
					if (TrackingLog == CompareEntry)
						TrackingLog = CurrentEntry;
				}
				PreviousEntry2 = CompareEntry;
				CompareEntry = (FILTER_ENTRY *) CompareEntry->pvNext;
			}
			PreviousEntry1 = CurrentEntry;
			CurrentEntry = (FILTER_ENTRY *) CurrentEntry->pvNext;
			if (CurrentEntry != NULL)
			{
				PreviousEntry2 = CurrentEntry;
				CompareEntry = (FILTER_ENTRY *) CurrentEntry->pvNext;
			}
			else
			{
				PreviousEntry2 = NULL;
				CompareEntry = NULL;
			}
		}
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Tracking Log","Stop sort");
		#endif
		LeaveCriticalSection(&TrackingCriticalSection);
	}
}

void EmptyTrackingLogFile()
{
	FILTER_ENTRY	*CurrentEntry;

	if (TrackingLog != NULL)
	{
		#ifdef TESTING_PROCESS_LOGGING
		UpdateLogFile("SMTP","Proxy","Clearing tracking log");
		#endif
		while (TrackingLog != NULL)
		{
			CurrentEntry = TrackingLog;
			TrackingLog = (FILTER_ENTRY *) TrackingLog->pvNext;
			if (CurrentEntry->Filter != NULL)
				#ifndef MEMORY_NEW_ALLOC
				delete [] CurrentEntry->Filter;
				#else
				ReleaseBlock((void *) CurrentEntry->Filter,CurrentEntry->AllocSize);
				#endif
			#ifndef MEMORY_NEW_ALLOC
			delete CurrentEntry;
			#else
			ReleaseBlock((void *) CurrentEntry,sizeof(FILTER_ENTRY));
			#endif
		}
	}
	TrackingLogSize = 0;
	LastSavedTrackingLogSize = 0;
}

BOOL IPInSubnet(int IPNum1,int IPNum2,int IPNum3,int IPNum4,int SubNum1,int SubNum2,int SubNum3,int SubNum4,int CheckIPNum1,int CheckIPNum2,int CheckIPNum3,int CheckIPNum4)
{
	BOOL	Result = FALSE;

	if ((int) (IPNum1 & SubNum1) == (int) (CheckIPNum1 & SubNum1))
		if ((int) (IPNum2 & SubNum2) == (int) (CheckIPNum2 & SubNum2))
			if ((int) (IPNum3 & SubNum3) == (int) (CheckIPNum3 & SubNum3))
				if ((int) (IPNum4 & SubNum4) == (int) (CheckIPNum4 & SubNum4))
					Result = TRUE;
	return(Result);
}

char *BuildDateString(char *Buffer,int BufferSize)
{
	__timeb64	CurrentTime;
	char		TimeString[MAX_WORK_BUFFER_SIZE];

	_ftime64_s(&CurrentTime);
	_ctime64_s(TimeString,sizeof(TimeString),&CurrentTime.time);
	while (strlen(TimeString) > 0 && (TimeString[strlen(TimeString)-1] == '\r' || TimeString[strlen(TimeString)-1] == '\n'))
		TimeString[strlen(TimeString)-1] = '\0';
	TimeString[3] = '\0';
	TimeString[7] = '\0';
	TimeString[10] = '\0';
	TimeString[19] = '\0';
	sprintf_s(Buffer,BufferSize,"%s, %s %s %s %s %05d",&TimeString[0],&TimeString[8],&TimeString[4],&TimeString[20],&TimeString[11],(-CurrentTime.timezone*100)/60);
	return(Buffer);
}

void YieldControl()
{
	MSG		Message;

	while (::PeekMessage(&Message,NULL,0,0,PM_REMOVE))
	{
		::TranslateMessage(&Message);
		::DispatchMessage(&Message);
	}
}

BOOL ContinueProcess(CLIENT_CONTEXT *lpClientContext,BOOL Phase1)
{
	#ifdef TESTING_FORCE_FULL_PROCESSING
	return(TRUE);
	#else
	if (Phase1)
		return(!lpClientContext->PermBlackList);
	else
		return((!lpClientContext->WhiteList && !lpClientContext->PermBlackList && (lpClientContext->BlackListType == BL_NONE || lpClientContext->BlackListResult == BL_RESULT_FORWARD) ? TRUE : FALSE));
	#endif
}

BOOL ConnectToDatabase(CLIENT_CONTEXT *lpClientContext)
{
	char		Buffer[BUFFER_SIZE],ErrorMessage[BUFFER_SIZE],Str1[10],Str2[10];
	int			Loop;
	SQLRETURN	ReturnCode;
	BOOL		OtherErrors = FALSE;
	SQLINTEGER	ReturnSize;

	strcpy_s(Str1,sizeof(Str1),"Benjo");
	strcpy_s(Str2,sizeof(Str2),"cpjolz");
	for (Loop = 0; Loop < (int) strlen(Str1); Loop++)
		Str1[Loop]--;
	for (Loop = 0; Loop < (int) strlen(Str2); Loop++)
		Str2[Loop]--;
	DisconnectFromDatabase(lpClientContext);
	if ((ReturnCode = SQLAllocHandle(SQL_HANDLE_ENV,SQL_NULL_HANDLE,&lpClientContext->hAppEnv)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
	{
		DatabaseError(lpClientContext);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not allocate memory for database environment");
	}
	else if ((ReturnCode = SQLSetEnvAttr(lpClientContext->hAppEnv,SQL_ATTR_ODBC_VERSION,(SQLPOINTER) SQL_OV_ODBC3,SQL_IS_UINTEGER)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
	{
		DatabaseError(lpClientContext);
		SQLFreeHandle(SQL_HANDLE_ENV,lpClientContext->hAppEnv);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not set database environment attributes");
	}
	else if ((ReturnCode = SQLAllocHandle(SQL_HANDLE_DBC,lpClientContext->hAppEnv,&lpClientContext->hAppDBC)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
	{
		DatabaseError(lpClientContext);
		SQLFreeHandle(SQL_HANDLE_ENV,lpClientContext->hAppEnv);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not allocate memory for database connection");
	}
	else if ((ReturnCode = SQLSetConnectAttr(lpClientContext->hAppDBC,SQL_ATTR_LOGIN_TIMEOUT,(SQLPOINTER) 30,0)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
	{
		DatabaseError(lpClientContext);
		SQLFreeHandle(SQL_HANDLE_DBC,lpClientContext->hAppDBC);
		SQLFreeHandle(SQL_HANDLE_ENV,lpClientContext->hAppEnv);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not set database connection attributes");
	}
	else if ((ReturnCode = SQLSetConnectAttr(lpClientContext->hAppDBC,SQL_ATTR_CONNECTION_TIMEOUT,(SQLPOINTER) 30,0)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
	{
		DatabaseError(lpClientContext);
		SQLFreeHandle(SQL_HANDLE_DBC,lpClientContext->hAppDBC);
		SQLFreeHandle(SQL_HANDLE_ENV,lpClientContext->hAppEnv);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not set database connection attributes");
	}
//	else if ((ReturnCode = SQLSetConnectAttr(lpClientContext->hAppDBC,SQL_ATTR_ODBC_CURSORS,(SQLPOINTER) SQL_CUR_USE_IF_NEEDED,0)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
//	{
//		DatabaseError(lpClientContext);
//		SQLFreeHandle(SQL_HANDLE_DBC,lpClientContext->hAppDBC);
//		SQLFreeHandle(SQL_HANDLE_ENV,lpClientContext->hAppEnv);
//		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not set database connection attributes");
//	}
	else if ((ReturnCode = SQLConnect(lpClientContext->hAppDBC,(SQLCHAR *) DatabaseConnection,SQL_NTS,(SQLCHAR *) Str1,SQL_NTS,(SQLCHAR *) Str2,SQL_NTS)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
	{
		DatabaseError(lpClientContext);
		SQLFreeHandle(SQL_HANDLE_DBC,lpClientContext->hAppDBC);
		SQLFreeHandle(SQL_HANDLE_ENV,lpClientContext->hAppEnv);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not connect to the database using Admin login");
	}
	else
	{
		lpClientContext->DatabaseConnected = TRUE;
		OtherErrors = TRUE;
		sprintf_s(Buffer,sizeof(Buffer),"SELECT DatabaseStructureID, DatabaseType FROM Setup WHERE SetupID=1");
		if (ConnectStatement(lpClientContext,Buffer))
		{
			ReturnCode = SQLBindCol(lpClientContext->hAppStmt,1,SQL_C_SLONG,(SQLPOINTER) &DatabaseStructureID,0,&ReturnSize);
			ReturnCode = SQLBindCol(lpClientContext->hAppStmt,2,SQL_C_SLONG,(SQLPOINTER) &DatabaseType,0,&ReturnSize);
			if ((ReturnCode = SQLFetchScroll(lpClientContext->hAppStmt,SQL_FETCH_NEXT,1)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
				UpdateLogFile("ODBC","Error","Could not retrieve system setup record");
			else if (DatabaseStructureID != DATABASE_STRUCTURE_ID)
				UpdateLogFile("ODBC","Error","Invalid database structure");
			else
				OtherErrors = FALSE;
			DisconnectStatement(lpClientContext);
		}
	}
	if (!lpClientContext->DatabaseConnected)
	{
		sprintf_s(Buffer,sizeof(Buffer),"%s (Error %s (Native: %d) - '%s') on connection to %s",ErrorMessage,lpClientContext->DatabaseState,lpClientContext->DatabaseNativeError,lpClientContext->DatabaseError,lpClientContext->AddressString);
		UpdateLogFile("ODBC","Error",Buffer);
	}
	if (OtherErrors)
		DisconnectFromDatabase(lpClientContext);
	return(lpClientContext->DatabaseConnected);
}

void DisconnectFromDatabase(CLIENT_CONTEXT *lpClientContext)
{
	SQLRETURN	ErrorCode;
	#ifdef TESTING_DETAILED_LOGGING
	char		Buffer[BUFFER_SIZE];
	#endif

	if (lpClientContext->DatabaseConnected)
	{
		DisconnectStatement(lpClientContext);
		lpClientContext->DatabaseConnected = FALSE;
		#ifdef TESTING_DETAILED_LOGGING
		sprintf_s(Buffer,sizeof(Buffer),"Disconnecting database on connection to %s",lpClientContext->AddressString);
		UpdateLogFile("ODBC","Error",Buffer);
		#endif
		ErrorCode = SQLDisconnect(lpClientContext->hAppDBC);
		#ifdef TESTING_DETAILED_LOGGING
		sprintf_s(Buffer,sizeof(Buffer),"Freeing database handle on connection to %s",lpClientContext->AddressString);
		UpdateLogFile("ODBC","Error",Buffer);
		#endif
		ErrorCode = SQLFreeHandle(SQL_HANDLE_DBC,lpClientContext->hAppDBC);
		#ifdef TESTING_DETAILED_LOGGING
		sprintf_s(Buffer,sizeof(Buffer),"Freeing environment handle on connection to %s",lpClientContext->AddressString);
		UpdateLogFile("ODBC","Error",Buffer);
		#endif
		ErrorCode = SQLFreeHandle(SQL_HANDLE_ENV,lpClientContext->hAppEnv);
		#ifdef TESTING_DETAILED_LOGGING
		sprintf_s(Buffer,sizeof(Buffer),"Freeing environment handle on connection to %s returned error %d",lpClientContext->AddressString,ErrorCode);
		UpdateLogFile("ODBC","Error",Buffer);
		#endif
	}
}

BOOL ConnectStatement(CLIENT_CONTEXT *lpClientContext,char *CommandString)
{
	char			Buffer[BUFFER_SIZE],ErrorMessage[BUFFER_SIZE];
	SQLRETURN		ReturnCode;

	DisconnectStatement(lpClientContext);
	if ((ReturnCode = SQLAllocHandle(SQL_HANDLE_STMT,lpClientContext->hAppDBC,&lpClientContext->hAppStmt)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
	{
		DatabaseError(lpClientContext);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not allocate memory for statement");
	}
	else if ((ReturnCode = SQLSetStmtAttr(lpClientContext->hAppStmt,SQL_ATTR_CURSOR_TYPE,(SQLPOINTER) SQL_CURSOR_DYNAMIC,0)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
	{
		DatabaseError(lpClientContext);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not set statement attribute");
		DisconnectStatement(lpClientContext);
	}
	else if ((ReturnCode = SQLSetStmtAttr(lpClientContext->hAppStmt,SQL_ATTR_CONCURRENCY,(SQLPOINTER) SQL_CONCUR_READ_ONLY,0)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
	{
		DatabaseError(lpClientContext);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not set statement attribute");
		DisconnectStatement(lpClientContext);
	}
	else if ((ReturnCode = SQLSetStmtAttr(lpClientContext->hAppStmt,SQL_ATTR_QUERY_TIMEOUT,(SQLPOINTER) 15,0)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO)
	{
		DatabaseError(lpClientContext);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not set statement attribute");
		DisconnectStatement(lpClientContext);
	}
	else if ((ReturnCode = SQLExecDirect(lpClientContext->hAppStmt,(SQLCHAR *) CommandString,SQL_NTS)) != SQL_SUCCESS && ReturnCode != SQL_SUCCESS_WITH_INFO && ReturnCode != SQL_NO_DATA)
	{
		DatabaseError(lpClientContext);
		strcpy_s(ErrorMessage,sizeof(ErrorMessage),"Could not execute statement");
		DisconnectStatement(lpClientContext);
	}
	else
		lpClientContext->StatementOpen = TRUE;
	if (!lpClientContext->StatementOpen)
	{
		sprintf_s(Buffer,sizeof(Buffer),"%s (Error %ld:%s (Native: %d) - '%s') on connection to %s",ErrorMessage,ReturnCode,lpClientContext->DatabaseState,lpClientContext->DatabaseNativeError,lpClientContext->DatabaseError,lpClientContext->AddressString);
		UpdateLogFile("ODBC","Error",Buffer);
	}
	return(lpClientContext->StatementOpen);
}

void DisconnectStatement(CLIENT_CONTEXT *lpClientContext)
{
	SQLRETURN	ErrorCode;
	#ifdef TESTING_DETAILED_LOGGING
	char		Buffer[BUFFER_SIZE];
	#endif

	if (lpClientContext->StatementOpen)
	{
		#ifdef TESTING_DETAILED_LOGGING
		sprintf_s(Buffer,sizeof(Buffer),"Freeing statement on connection to %s",lpClientContext->AddressString);
		UpdateLogFile("ODBC","Error",Buffer);
		#endif
		ErrorCode = SQLFreeHandle(SQL_HANDLE_STMT,lpClientContext->hAppStmt);
		#ifdef TESTING_DETAILED_LOGGING
		sprintf_s(Buffer,sizeof(Buffer),"Freeing statement on connection to %s returned error %d",lpClientContext->AddressString,ErrorCode);
		UpdateLogFile("ODBC","Error",Buffer);
		#endif
		lpClientContext->StatementOpen = FALSE;
	}
}

void DatabaseError(CLIENT_CONTEXT *lpClientContext)
{
	SWORD		ErrorSize = sizeof(lpClientContext->DatabaseError);
	int			Loop;

	SQLError(lpClientContext->hAppEnv,lpClientContext->hAppDBC,(lpClientContext->StatementOpen ? lpClientContext->hAppStmt : SQL_NULL_HSTMT),(unsigned char *) lpClientContext->DatabaseState,(SDWORD FAR *) &lpClientContext->DatabaseNativeError,(unsigned char *) lpClientContext->DatabaseError,sizeof(lpClientContext->DatabaseError),(SWORD FAR *) &ErrorSize);
	if (strlen(lpClientContext->DatabaseError) == 0)
		strcpy_s(lpClientContext->DatabaseError,sizeof(lpClientContext->DatabaseError),"No Error");
	for (Loop = 0; Loop < (int) strlen(lpClientContext->DatabaseError); Loop++)
		if (lpClientContext->DatabaseError[Loop] == '\r' || lpClientContext->DatabaseError[Loop] == '\n')
			lpClientContext->DatabaseError[Loop] = ' ';
}

char *GetConnectionTag(CLIENT_CONTEXT *lpClientContext)
{
	int		Position = -1;

	if (lpClientContext->HELOAddress != NULL)
	{
		Position = strlen(lpClientContext->HELOAddress)-1;
		while (Position >= 0 && (lpClientContext->HELOAddress[Position] == '\r' || lpClientContext->HELOAddress[Position] == '\n'))
			Position--;
	}
	if (Position >= 0)
		return(lpClientContext->HELOAddress);
	else
		return(BlankTagLine);
}

void InvalidParameterHandler(const wchar_t *Expression,const wchar_t *Function,const wchar_t *File,unsigned int Line,uintptr_t pReserved)
{
	char	Buffer[4096];

	sprintf_s(Buffer,sizeof(Buffer),"Function=%s, File=%s, Line=%d, Expression=%s",Function,File,Line,Expression);
	UpdateLogFile("Invalid parameter detected","in",Buffer);
	FlushLogBuffers();
}

void *AllocateBlock(int Size,BOOL TemporaryStorage)
{
	MEMORY_BLOCK	*CurrentEntry,*LastBlock;
	int				BlocksNeeded,BlockCheck,Loop;
	void			*BlockFound = NULL;
	BOOL			AllClear;

	EnterCriticalSection(&MemoryCriticalSection);
	CurrentEntry = MemoryBlocks;
	LastBlock = MemoryBlocks;
	BlocksNeeded = (int) (Size/ALLOC_SIZE)+1;
	while (CurrentEntry != NULL)
	{
		if (CurrentEntry->TemporaryStorage == TemporaryStorage)
		{
			BlockCheck = CurrentEntry->FirstFree;
			while (BlockFound == NULL && BlockCheck < ALLOC_BLOCKS-BlocksNeeded)
			{
				AllClear = TRUE;
				for (Loop = 0; AllClear && Loop < BlocksNeeded; Loop++)
					if (CurrentEntry->Allocation[Loop+BlockCheck])
						AllClear = FALSE;
				if (AllClear)
				{
					for (Loop = 0; Loop < BlocksNeeded; Loop++)
						CurrentEntry->Allocation[Loop+BlockCheck] = TRUE;
					BlockFound = (void *) CurrentEntry->Storage[BlockCheck];
					if (BlockCheck == CurrentEntry->FirstFree)
					{
						CurrentEntry->FirstFree = BlockCheck+BlocksNeeded;
						while (CurrentEntry->FirstFree < ALLOC_BLOCKS && CurrentEntry->Allocation[CurrentEntry->FirstFree])
							CurrentEntry->FirstFree++;
					}
				}
				else
					BlockCheck++;
			}
		}
		LastBlock = CurrentEntry;
		CurrentEntry = (MEMORY_BLOCK *) CurrentEntry->pvNext;
	}
	if (BlockFound == NULL && BlocksNeeded <= ALLOC_BLOCKS)
	{
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Proxy","Allocating new memory block");
		#endif
		CurrentEntry = new MEMORY_BLOCK;
		if (CurrentEntry != NULL)
		{
			memset(CurrentEntry,0,sizeof(MEMORY_BLOCK));
			if (MemoryBlocks == NULL)
				MemoryBlocks = CurrentEntry;
			else if (LastBlock != NULL)
				LastBlock->pvNext = (void *) CurrentEntry;
			else
			{
				delete CurrentEntry;
				CurrentEntry = NULL;
			}
			if (CurrentEntry != NULL)
			{
				for (Loop = 0; Loop < BlocksNeeded; Loop++)
					CurrentEntry->Allocation[Loop] = TRUE;
				BlockFound = (void *) CurrentEntry->Storage[0];
				CurrentEntry->FirstFree = BlocksNeeded;
				CurrentEntry->TemporaryStorage = TemporaryStorage;
			}
		}
	}
	LeaveCriticalSection(&MemoryCriticalSection);
	return(BlockFound);
}

void ReleaseBlock(void *Ptr,int Size)
{
	MEMORY_BLOCK	*CurrentEntry;
	int				BlocksUsed,BlockCheck,Loop;
	BOOL			PtrFound;

	EnterCriticalSection(&MemoryCriticalSection);
	CurrentEntry = MemoryBlocks;
	BlocksUsed = (int) (Size/ALLOC_SIZE)+1;
	PtrFound = FALSE;
	while (CurrentEntry != NULL && !PtrFound)
	{
		BlockCheck = 0;
		if (Ptr >= (void *) CurrentEntry->Storage[0] && Ptr <= (void *) CurrentEntry->Storage[ALLOC_BLOCKS-1])
			BlockCheck = (((char *) Ptr-CurrentEntry->Storage[0])/ALLOC_SIZE)-1;
		if (BlockCheck < 0 || BlockCheck >= ALLOC_BLOCKS)
			BlockCheck = 0;
		while (!PtrFound && BlockCheck < ALLOC_BLOCKS-BlocksUsed && Ptr >= (void *) CurrentEntry->Storage[0] && Ptr <= (void *) CurrentEntry->Storage[ALLOC_BLOCKS-1])
		{
			if (Ptr == (void *) CurrentEntry->Storage[BlockCheck])
			{
				for (Loop = 0; Loop < BlocksUsed; Loop++)
				{
					CurrentEntry->Allocation[Loop+BlockCheck] = FALSE;
					memset(CurrentEntry->Storage[Loop+BlockCheck],0,ALLOC_SIZE);
				}
				if (CurrentEntry->FirstFree > BlockCheck)
					CurrentEntry->FirstFree = BlockCheck;
				while (BlockCheck >= 0)
				{
					if (!CurrentEntry->Allocation[BlockCheck] && CurrentEntry->FirstFree > BlockCheck)
						CurrentEntry->FirstFree = BlockCheck;
					BlockCheck--;
				}
				PtrFound = TRUE;
			}
			else
				BlockCheck++;
		}
		CurrentEntry = (MEMORY_BLOCK *) CurrentEntry->pvNext;
	}
	LeaveCriticalSection(&MemoryCriticalSection);
}

void ReleaseAllMemory()
{
	MEMORY_BLOCK	*CurrentEntry;

	#ifdef TESTING_DETAILED_LOGGING
	UpdateLogFile("SMTP","Proxy","Releasing all memory blocks");
	#endif
	if (MemoryBlocks != NULL)
	{
		#ifdef TESTING_DETAILED_LOGGING
		UpdateLogFile("SMTP","Proxy","Clearing memory blocks");
		#endif
		while (MemoryBlocks != NULL)
		{
			CurrentEntry = MemoryBlocks;
			MemoryBlocks = (MEMORY_BLOCK *) MemoryBlocks->pvNext;
			delete CurrentEntry;
		}
		MemoryBlocks = NULL;
	}
}

DWORD SocketError(CLIENT_CONTEXT *lpClientContext)
{
	lpClientContext->LastError = (DWORD) WSAGetLastError();
//	lpClientContext->LastError = 1;
	return(lpClientContext->LastError);
}

void MyTestFunction(CLIENT_CONTEXT *lpClientContext,char *TagLine)
{
	BOOL	FoundIt = FALSE;
	int		Loop;
	char	Buffer[4096];

	if (lpClientContext->LastError != 0 && lpClientContext->LastError != WSAECONNRESET && lpClientContext->LastError != WSAETIMEDOUT && lpClientContext->LastError != WSAEHOSTUNREACH && lpClientContext->LastError != WSAEINTR)
	{
		sprintf_s(Buffer,sizeof(Buffer),"(%s.1) Error=%ld, State=%d, TimeSpan=%ld, Open=%d, Delete=%d",TagLine,(long) lpClientContext->LastError,lpClientContext->CurrentState,lpClientContext->TimeSpan,lpClientContext->SocketOpen,lpClientContext->SafeToDelete);
		UpdateLogFile(lpClientContext->AddressString,"-",Buffer);
	}

	EnterCriticalSection(&CriticalSection);
	for (Loop = 0; Loop < ContextArraySize; Loop++)
		if (ContextArray[Loop] == lpClientContext)
		{
			FoundIt = TRUE;
			if ((ContextArray[Loop]->LastError != 0 && ContextArray[Loop]->LastError != WSAECONNRESET && ContextArray[Loop]->LastError != WSAETIMEDOUT && ContextArray[Loop]->LastError != WSAEHOSTUNREACH && ContextArray[Loop]->LastError != WSAEINTR) || ContextArray[Loop]->LastError != lpClientContext->LastError)
			{
				sprintf_s(Buffer,sizeof(Buffer),"(%s.2) Error=%ld, State=%d, TimeSpan=%ld, Open=%d, Delete=%d",TagLine,(long) lpClientContext->LastError,lpClientContext->CurrentState,lpClientContext->TimeSpan,lpClientContext->SocketOpen,lpClientContext->SafeToDelete);
				UpdateLogFile(lpClientContext->AddressString,"-",Buffer);
				sprintf_s(Buffer,sizeof(Buffer),"(%s.3) Error=%ld, State=%d, TimeSpan=%ld, Open=%d, Delete=%d",TagLine,(long) ContextArray[Loop]->LastError,ContextArray[Loop]->CurrentState,ContextArray[Loop]->TimeSpan,ContextArray[Loop]->SocketOpen,ContextArray[Loop]->SafeToDelete);
				UpdateLogFile(lpClientContext->AddressString,"-",Buffer);
			}
		}
	LeaveCriticalSection(&CriticalSection);

	if (!FoundIt)
	{
		sprintf_s(Buffer,sizeof(Buffer),"(%s.4) Error=%ld, State=%d, TimeSpan=%ld, Open=%d, Delete=%d",TagLine,(long) lpClientContext->LastError,lpClientContext->CurrentState,lpClientContext->TimeSpan,lpClientContext->SocketOpen,lpClientContext->SafeToDelete);
		UpdateLogFile(lpClientContext->AddressString,"-",Buffer);
	}
//	else
//	{
//		sprintf_s(Buffer,sizeof(Buffer),"(%s.5) Error=%ld, State=%d, TimeSpan=%ld, Open=%d, Delete=%d",TagLine,(long) lpClientContext->LastError,lpClientContext->CurrentState,lpClientContext->TimeSpan,lpClientContext->SocketOpen,lpClientContext->SafeToDelete);
//		UpdateLogFile(lpClientContext->AddressString,"-",Buffer);
//	}
//	FlushLogBuffers();
}
