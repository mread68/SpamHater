// SMTPServ.cpp
//
// Implementation of CSMTPService

#include "SMTPApp.h"

// static variables
CSMTPService		*CSMTPService::m_pThis = NULL;
BOOL				ServiceTerminating = TRUE,ServicePaused = FALSE;

CSMTPService::CSMTPService(const char* szServiceName)
{
	// copy the address of the current object so we can access it from
	// the static member callback functions.
	// WARNING: This limits the application to only one CSMTPService object.
	m_pThis = this;

	// Set the default service name and version
	strncpy_s(m_szServiceName,szServiceName,sizeof(m_szServiceName)-1);
	m_iMajorVersion = 1;
	m_iMinorVersion = 0;
	m_hEventSource = NULL;

	// set up the initial service status
	m_hServiceStatus = NULL;
	m_Status.dwServiceType = SERVICE_WIN32_OWN_PROCESS;
	m_Status.dwCurrentState = SERVICE_STOPPED;
	m_Status.dwControlsAccepted = SERVICE_ACCEPT_STOP;
	m_Status.dwWin32ExitCode = 0;
	m_Status.dwServiceSpecificExitCode = 0;
	m_Status.dwCheckPoint = 0;
	m_Status.dwWaitHint = 0;
	ServiceTerminating = TRUE;
	ServicePaused = FALSE;
}

CSMTPService::~CSMTPService()
{
	#ifdef _DEBUG
	DebugMsg("CSMTPService::~CSMTPService()");
	#endif
	if (m_hEventSource)
	{
		::DeregisterEventSource(m_hEventSource);
	}
}

////////////////////////////////////////////////////////////////////////////////////////
// Default command line argument parsing

// Returns TRUE if it found an arg it recognised, FALSE if not
// Note: processing some arguments causes output to stdout to be generated.
BOOL CSMTPService::ParseStandardArgs(int argc,char* argv[])
{
	// See if we have any command line args we recognise
	if (argc <= 1)
		return(FALSE);

	if (_stricmp(argv[1], "-v") == 0)
	{
		// Spit out version info
		printf("%s Version %d.%d\n",m_szServiceName,m_iMajorVersion,m_iMinorVersion);
		printf("The service is %s installed\n",IsInstalled() ? "currently" : "not");
		return(TRUE); // say we processed the argument
	}
	else if (_stricmp(argv[1], "-i") == 0)
	{
		// Request to install.
		if (IsInstalled())
			printf("%s is already installed\n",m_szServiceName);
		else
		{
			// Try and install the copy that's running
			if (Install())
				printf("%s installed\n",m_szServiceName);
			else
				printf("%s failed to install. Error %ld\n",m_szServiceName,GetLastError());
		}
		return(TRUE); // say we processed the argument
	}
	else if (_stricmp(argv[1],"-u") == 0)
	{
		// Request to uninstall.
		if (!IsInstalled())
			printf("%s is not installed\n", m_szServiceName);
		else
		{
			// Try and remove the copy that's installed
			if (Uninstall())
			{
				// Get the executable file path
				char szFilePath[_MAX_PATH];
				::GetModuleFileName(NULL, szFilePath, sizeof(szFilePath));
				printf("%s removed. (You must delete the file (%s) yourself.)\n",m_szServiceName,szFilePath);
			}
			else
				printf("Could not remove %s. Error %ld\n",m_szServiceName,GetLastError());
		}
		return(TRUE); // say we processed the argument
	}

	// Don't recognise the args
	return(FALSE);
}

////////////////////////////////////////////////////////////////////////////////////////
// Install/uninstall routines

// Test if the service is currently installed
BOOL CSMTPService::IsInstalled()
{
	BOOL bResult = FALSE;

	// Open the Service Control Manager
	SC_HANDLE hSCM = ::OpenSCManager(NULL,NULL,SC_MANAGER_ALL_ACCESS); // full access
	if (hSCM)
	{
		// Try to open the service
		SC_HANDLE hService = ::OpenService(hSCM,m_szServiceName,SERVICE_QUERY_CONFIG);
		if (hService)
		{
			bResult = TRUE;
			::CloseServiceHandle(hService);
		}
		::CloseServiceHandle(hSCM);
	}
	return(bResult);
}

BOOL CSMTPService::Install()
{
	char		szFilePath[_MAX_PATH],szKey[1024];
	SC_HANDLE	hSCM,hService;
	HKEY		hKey = NULL;
	DWORD		dwData;

	// Open the Service Control Manager
	hSCM = ::OpenSCManager(NULL,NULL,SC_MANAGER_ALL_ACCESS); // full access
	if (!hSCM)
		return(FALSE);

	// Get the executable file path
	::GetModuleFileName(NULL,szFilePath,sizeof(szFilePath));

	// Create the service
	hService = ::CreateService(hSCM,m_szServiceName,m_szServiceName,SERVICE_ALL_ACCESS,SERVICE_WIN32_OWN_PROCESS,SERVICE_DEMAND_START,SERVICE_ERROR_NORMAL,szFilePath,NULL,NULL,NULL,NULL,NULL);
	if (!hService)
	{
		::CloseServiceHandle(hSCM);
		return(FALSE);
	}

	// make registry entries to support logging messages
	// Add the source name as a subkey under the Application
	// key in the EventLog service portion of the registry.
	strcpy_s(szKey,sizeof(szKey),"SYSTEM\\CurrentControlSet\\Services\\EventLog\\Application\\");
	strcat_s(szKey,sizeof(szKey),m_szServiceName);
	if (::RegCreateKey(HKEY_LOCAL_MACHINE, szKey, &hKey) != ERROR_SUCCESS)
	{
		::CloseServiceHandle(hService);
		::CloseServiceHandle(hSCM);
		return(FALSE);
	}

	// Add the Event ID message-file name to the 'EventMessageFile' subkey.
	::RegSetValueEx(hKey,"EventMessageFile",0,REG_EXPAND_SZ,(CONST BYTE *) szFilePath,strlen(szFilePath)+1);

	// Set the supported types flags.
	dwData = EVENTLOG_ERROR_TYPE | EVENTLOG_WARNING_TYPE | EVENTLOG_INFORMATION_TYPE;
	::RegSetValueEx(hKey,"TypesSupported",0,REG_DWORD,(CONST BYTE *) &dwData,sizeof(DWORD));
	::RegCloseKey(hKey);

	LogEvent(EVENTLOG_INFORMATION_TYPE,EVMSG_INSTALLED,m_szServiceName);

	// tidy up
	::CloseServiceHandle(hService);
	::CloseServiceHandle(hSCM);
	return(TRUE);
}

BOOL CSMTPService::Uninstall()
{
	// Open the Service Control Manager
	SC_HANDLE hSCM = ::OpenSCManager(NULL,NULL,SC_MANAGER_ALL_ACCESS);
	if (!hSCM)
		return(FALSE);

	BOOL bResult = FALSE;
	SC_HANDLE hService = ::OpenService(hSCM,m_szServiceName,DELETE);
	if (hService)
	{
		if (::DeleteService(hService))
		{
			LogEvent(EVENTLOG_INFORMATION_TYPE,EVMSG_REMOVED,m_szServiceName);
			bResult = TRUE;
		}
		else
		{
			LogEvent(EVENTLOG_ERROR_TYPE,EVMSG_NOTREMOVED,m_szServiceName);
		}
		::CloseServiceHandle(hService);
	}
	::CloseServiceHandle(hSCM);
	return(bResult);
}

///////////////////////////////////////////////////////////////////////////////////////
// Logging functions

// This function makes an entry into the application event log
void CSMTPService::LogEvent(WORD wType,DWORD dwID,const char *pszS1,const char *pszS2,const char *pszS3)
{
	const char	*ps[3];
	int			Loop,iStr = 0;

	ps[0] = pszS1;
	ps[1] = pszS2;
	ps[2] = pszS3;
	for (Loop = 0; Loop < 3; Loop++)
		if (ps[Loop] != NULL)
			iStr++;

	// Check the event source has been registered and if not then register it now
	if (!m_hEventSource)
		m_hEventSource = ::RegisterEventSource(NULL,m_szServiceName);

	if (m_hEventSource)
		::ReportEvent(m_hEventSource,wType,0,dwID,NULL,iStr,0,ps,NULL);
}

//////////////////////////////////////////////////////////////////////////////////////////////
// Service startup and registration

BOOL CSMTPService::StartService()
{
	SERVICE_TABLE_ENTRY		Service[] = {{m_szServiceName,ServiceMain},{NULL,NULL}};
	BOOL					Result;

	#ifdef _DEBUG
	DebugMsg("Calling StartServiceCtrlDispatcher()");
	#endif
	Result = ::StartServiceCtrlDispatcher(Service);
	#ifdef _DEBUG
	DebugMsg("Returned from StartServiceCtrlDispatcher()");
	#endif
	return(Result);
}

// static member function (callback)
void CSMTPService::ServiceMain(DWORD dwArgc,LPTSTR *lpszArgv)
{
	// Get a pointer to the C++ object
	CSMTPService		*pService = m_pThis;

	#ifdef _DEBUG
	pService->DebugMsg("Entering CSMTPService::ServiceMain()");
	#endif
	// Register the control request handler
	pService->m_Status.dwCurrentState = SERVICE_START_PENDING;
	pService->m_hServiceStatus = RegisterServiceCtrlHandler(pService->m_szServiceName,Handler);
	if (pService->m_hServiceStatus == NULL)
	{
		pService->LogEvent(EVENTLOG_ERROR_TYPE,EVMSG_CTRLHANDLERNOTINSTALLED);
		exit(1);
	}

	// Start the initialisation
	if (pService->Initialize())
	{
		// Do the real work.
		// When the Run function returns, the service has stopped.
		ServiceTerminating = FALSE;
		ServicePaused = FALSE;
		pService->m_Status.dwWin32ExitCode = 0;
		pService->m_Status.dwCheckPoint = 0;
		pService->m_Status.dwWaitHint = 0;
		pService->Run();
	}
	#ifdef _DEBUG
	pService->DebugMsg("Leaving CSMTPService::ServiceMain()");
	#endif
	pService->LogEvent(EVENTLOG_INFORMATION_TYPE,EVMSG_STOPPED);
	pService->SetStatus(SERVICE_STOPPED);
	Sleep(1000);
	exit(0);
}

///////////////////////////////////////////////////////////////////////////////////////////
// status functions

void CSMTPService::SetStatus(DWORD dwState)
{
	#ifdef _DEBUG
	DebugMsg("CSMTPService::SetStatus(%lu, %lu)",m_hServiceStatus,dwState);
	#endif
	m_Status.dwCurrentState = dwState;
	::SetServiceStatus(m_hServiceStatus,&m_Status);
}

///////////////////////////////////////////////////////////////////////////////////////////
// Service initialization

BOOL CSMTPService::Initialize()
{
	#ifdef _DEBUG
	DebugMsg("Entering CSMTPService::Initialize()");
	#endif

	// Start the initialization
	SetStatus(SERVICE_START_PENDING);

	// Perform the actual initialization
	BOOL bResult = OnInit();

	// Set final state
	m_Status.dwWin32ExitCode = GetLastError();
	m_Status.dwCheckPoint = 0;
	m_Status.dwWaitHint = 0;
	if (!bResult)
	{
		LogEvent(EVENTLOG_ERROR_TYPE,EVMSG_FAILEDINIT);
		SetStatus(SERVICE_STOPPED);
		return(FALSE);
	}

	LogEvent(EVENTLOG_INFORMATION_TYPE,EVMSG_STARTED);
	SetStatus(SERVICE_RUNNING);

	#ifdef _DEBUG
	DebugMsg("Leaving CSMTPService::Initialize()");
	#endif
	return(TRUE);
}

///////////////////////////////////////////////////////////////////////////////////////////////
// main function to do the real work of the service

// This function performs the main work of the service.
// When this function returns the service has stopped.
void CSMTPService::Run()
{
	#ifdef _DEBUG
	DebugMsg("Entering CSMTPService::Run()");
	#endif

	while (!ServiceTerminating)
	{
		#ifdef _DEBUG
		DebugMsg("Sleeping...");
		#endif
		Sleep(5000);
	}

	// nothing more to do
	#ifdef _DEBUG
	DebugMsg("Leaving CSMTPService::Run()");
	#endif
}

//////////////////////////////////////////////////////////////////////////////////////
// Control request handlers

// static member function (callback) to handle commands from the
// service control manager
void CSMTPService::Handler(DWORD dwOpcode)
{
	// Get a pointer to the object
	CSMTPService		*pService = m_pThis;

	#ifdef _DEBUG
	pService->DebugMsg("CSMTPService::Handler(%lu)", dwOpcode);
	#endif
	switch (dwOpcode)
	{
		case SERVICE_CONTROL_STOP:			pService->SetStatus(SERVICE_STOP_PENDING);
											pService->OnStop();
											break;
		case SERVICE_CONTROL_PAUSE:			pService->OnPause();
											pService->LogEvent(EVENTLOG_INFORMATION_TYPE,EVMSG_PAUSED);
											break;
		case SERVICE_CONTROL_CONTINUE:		pService->OnContinue();
											pService->LogEvent(EVENTLOG_INFORMATION_TYPE,EVMSG_CONTINUED);
											break;
		case SERVICE_CONTROL_INTERROGATE:	pService->OnInterrogate();
											break;
		case SERVICE_CONTROL_SHUTDOWN:		pService->OnShutdown();
											break;
		default:							if (dwOpcode >= SERVICE_CONTROL_USER)
											{
												if (!pService->OnUserControl(dwOpcode))
												{
													pService->LogEvent(EVENTLOG_ERROR_TYPE,EVMSG_BADREQUEST);
												}
											}
											else
											{
												pService->LogEvent(EVENTLOG_ERROR_TYPE,EVMSG_BADREQUEST);
											}
											break;
	}

	// Report current status
	#ifdef _DEBUG
	pService->DebugMsg("Updating status (%lu, %lu)",pService->m_hServiceStatus,pService->m_Status.dwCurrentState);
	#endif
	::SetServiceStatus(pService->m_hServiceStatus, &pService->m_Status);
}

// Called when the service is first initialized
BOOL CSMTPService::OnInit()
{
	#ifdef _DEBUG
	DebugMsg("CSMTPService::OnInit()");
	#endif
	return(TRUE);
}

// Called when the service control manager wants to stop the service
void CSMTPService::OnStop()
{
	#ifdef _DEBUG
	DebugMsg("CSMTPService::OnStop()");
	#endif
}

// called when the service is interrogated
void CSMTPService::OnInterrogate()
{
	#ifdef _DEBUG
	DebugMsg("CSMTPService::OnInterrogate()");
	#endif
}

// called when the service is paused
void CSMTPService::OnPause()
{
	#ifdef _DEBUG
	DebugMsg("CSMTPService::OnPause()");
	#endif
}

// called when the service is continued
void CSMTPService::OnContinue()
{
	#ifdef _DEBUG
	DebugMsg("CSMTPService::OnContinue()");
	#endif
}

// called when the service is shut down
void CSMTPService::OnShutdown()
{
	#ifdef _DEBUG
	DebugMsg("CSMTPService::OnShutdown()");
	#endif
}

// called when the service gets a user control message
BOOL CSMTPService::OnUserControl(DWORD dwOpcode)
{
	#ifdef _DEBUG
	DebugMsg("CSMTPService::OnUserControl(%8.8lXH)",dwOpcode);
	#endif
	return(FALSE); // say not handled
}

////////////////////////////////////////////////////////////////////////////////////////////
// Debugging support

void CSMTPService::DebugMsg(const char *pszFormat,...)
{
	char		buf[1024];
	va_list		arglist;

	sprintf_s(buf,sizeof(buf),"[%s](%lu): ",m_szServiceName,GetCurrentThreadId());
	va_start(arglist,pszFormat);
	vsprintf_s(&buf[strlen(buf)],sizeof(buf)-strlen(buf)-1,pszFormat,arglist);
	va_end(arglist);
	LogEvent(EVENTLOG_WARNING_TYPE,EVMSG_DEBUG,buf);
}
