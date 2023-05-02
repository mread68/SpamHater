// SMTPCtrl.h
#include "sys\timeb.h"

#define STATE_HELO					1
#define STATE_MAIL					2
#define STATE_RCPT					3
#define STATE_DATA					4
#define STATE_PROCESS				5
#define STATE_FORWARD				6
#define STATE_QUIT					7

#define COMMAND_UNKNOWN				0
#define COMMAND_HELO				1
#define COMMAND_EHLO				2
#define COMMAND_MAIL				3
#define COMMAND_RCPT				4
#define COMMAND_DATA				5
#define COMMAND_HELP				6
#define COMMAND_QUIT				7
#define COMMAND_NOOP				8
#define COMMAND_RSET				9
#define COMMAND_FROM				10
#define COMMAND_TO					11
#define COMMAND_STAT				12
#define COMMAND_KILL				13
#define COMMAND_WLST				14
#define COMMAND_BLST				15
#define COMMAND_CTRK				16
#define COMMAND_LTRK				17
#define COMMAND_STRK				18
#define COMMAND_HOLD				19
#define COMMAND_CSTA				20
#define COMMAND_COBK				21
#define COMMAND_VRFY				22
#define COMMAND_LCFG				23

#define COMMAND_HELO_LEN			69
#define COMMAND_EHLO_LEN			COMMAND_HELO_LEN
#define COMMAND_MAIL_LEN			264
#define COMMAND_RCPT_LEN			264
#define COMMAND_DATA_LEN			4
#define COMMAND_HELP_LEN			4
#define COMMAND_QUIT_LEN			4
#define COMMAND_NOOP_LEN			4
#define COMMAND_RSET_LEN			4
#define COMMAND_FROM_LEN			COMMAND_MAIL_LEN
#define COMMAND_TO_LEN				COMMAND_RCPT_LEN
#define COMMAND_STAT_LEN			4
#define COMMAND_KILL_LEN			12
#define COMMAND_WLST_LEN			12
#define COMMAND_BLST_LEN			12
#define COMMAND_CTRK_LEN			4
#define COMMAND_LTRK_LEN			4
#define COMMAND_STRK_LEN			4
#define COMMAND_HOLD_LEN			4
#define COMMAND_CSTA_LEN			4
#define COMMAND_COBK_LEN			4
#define COMMAND_VRFY_LEN			264
#define COMMAND_LCFG_LEN			4

#define BL_NONE						0
#define BL_IP						1
#define BL_DOMAIN					2
#define BL_KEYWORD					3
#define BL_TAG						4
#define BL_FORMAT					5
#define BL_RESULT_TURFDIR			0
#define BL_RESULT_FORWARD			1
#define BL_RESULT_DELETE			2
#define BL_RESULT_DENY				3

#define BL_TOTAL_STATS				6
#define BL_TOTAL_SUB_STATS			5
#define BL_SUB_TOTAL				0
#define BL_SUB_IP_CONNECT			1
#define BL_SUB_IP_DOMAIN			2
#define BL_SUB_IP_HTML				3
#define BL_SUB_IP_DNSBL				4
#define BL_SUB_DOMAIN_ADDRESS		1
#define BL_SUB_DOMAIN_SUSPECT		2
#define BL_SUB_DOMAIN_REVERSE		3
#define BL_SUB_KEYWORD_SUBJECT		1
#define BL_SUB_KEYWORD_BODY			2
#define BL_SUB_TAG_HEADER			1
#define BL_SUB_TAG_ADMIN			2
#define BL_SUB_FORMAT_FROM			1
#define BL_SUB_FORMAT_BODY			2

#define SEARCH_PREFIX				0
#define SEARCH_SUFFIX				1
#define SEARCH_CONTAINS				2
#define SEARCH_EXACT				3

#define COMMAND_MAX_RCPT			1000
#define MAX_CONTEXT					300
#define MAX_LOG_BUFFER				102400
#define MAX_LOG_BUFFER_THRESHOLD	10240
#define MAX_MESSAGE_SIZE			520000
#define MAX_PATH_SIZE				_MAX_PATH
#define MAX_KEYWORD_SIZE			2048
#define MAX_KEYVALUE_SIZE			20480
#define MAX_WORK_BUFFER_SIZE		1024
#define MAX_MESSAGE_BUFFER			5120
#define MAX_REJECT_TAGS				200
#define MAX_DNSBL_SOURCES			200
#define MAX_BOUNDARIES				3
#define MAX_HTML_RECORDS			10
#define BUFFER_SIZE					51200
#define ALLOC_SIZE					25
#define ALLOC_BLOCKS				80000

typedef struct _MEMORY_BLOCK
{
	BOOL		Allocation[ALLOC_BLOCKS],TemporaryStorage;
	int			FirstFree;
	char		Storage[ALLOC_BLOCKS][ALLOC_SIZE];
	LPVOID		pvNext;
} MEMORY_BLOCK;

typedef struct _FILTER_ENTRY
{
	char		*Filter;
	int			AllocSize;
	LPVOID		pvNext;
} FILTER_ENTRY;

typedef struct _CLIENT_CONTEXT
{
	SOCKET				Socket,HostSocket;
	BOOL				SocketOpen,HostSocketOpen,SafeToDelete,SendComplete,ProcessFilterExecuted;
	long				ConnectionID,BufferPosition;
	HANDLE				ThreadHandle;
	WSAOVERLAPPED		Overlapped;
	char				Buffer[BUFFER_SIZE];
	int					CurrentState;
	DWORD				LastError,TimeSpan,ThreadID;
	__time64_t			LastAccess;
	struct __timeb64	StartTime,EndTime;
	SOCKADDR			ConnectionAddress;
	char				AddressString[30];
	char				*HELOAddress,HELOcmd[COMMAND_HELO_LEN+1];
	char				MAILcmd[COMMAND_MAIL_LEN+1],MAILAddress[COMMAND_MAIL_LEN+1];
	char				*RCPTcmd[COMMAND_MAX_RCPT],*RCPTAddress[COMMAND_MAX_RCPT];
	int					RCPTCount,BlackListType,BlackListSubType,BlackListResult,SuspectResult,HTMLLinks,HTMLLinksResolved,WhiteRecipient,RCPTcmdSize[COMMAND_MAX_RCPT];
	FILE				*MessageFile,*TurfFile;
	BOOL				FileOpen,TurfFileOpen,ForwardComplete,WhiteList,MessageTruncated,MultiPartMessage,TerminationMessage;
	BOOL				Timeout,MessageIncomplete,EmptyMessage,PermBlackList,SuspectDomain,EndOfMessageBoundary,ThreadStarted,ThreadExited;
	char				FileName[MAX_PATH_SIZE],FullFileName[MAX_PATH_SIZE],TurfFileName[MAX_PATH_SIZE],StepsTaken[30];
	long				MessageSize,AllocatedSize,ScanSize,ScanPosition;
	char				LastChars[6],FilteredBy[MAX_WORK_BUFFER_SIZE];
	char				SubjectLine[MAX_KEYWORD_SIZE],FromField[MAX_KEYWORD_SIZE],MessageID[MAX_KEYWORD_SIZE];
	char				Boundary[MAX_BOUNDARIES][MAX_KEYWORD_SIZE];
	int					CurrentBoundary,ScanStep,CharReplacements,HTMLAddrCount,ClientErrorCount;
	BYTE				HTMLAddr[MAX_HTML_RECORDS+1][4];
	char				*MessageBody;
	SQLHENV				hAppEnv;						// ODBC environment
	SQLHDBC				hAppDBC;						// ODBC database connection
	SQLHSTMT			hAppStmt;						// ODBC statment
	BOOL				DatabaseConnected,StatementOpen,MessageIdentified;
	char				DatabaseError[BUFFER_SIZE];		// Last ODBC error
	char				DatabaseState[BUFFER_SIZE];		// Last ODBC state
	SDWORD				DatabaseNativeError;			// Last ODBC native error code
	char				DBStrField1[MAX_WORK_BUFFER_SIZE],DBStrField2[MAX_WORK_BUFFER_SIZE];
	SQLINTEGER			DBStrField1Size,DBStrField2Size;
} CLIENT_CONTEXT;

class CSMTPControl : public CSMTPService
{
public:
	CSMTPControl();
	virtual BOOL OnInit();
	virtual void Run();
	virtual void OnStop();
	virtual void OnPause();
	virtual void OnContinue();
	virtual BOOL OnUserControl(DWORD dwOpcode);
	BOOL InitializeSockets();
	void CloseSockets(BOOL Graceful);
	BOOL InitializeThreads();
	BOOL InitializeThread(CLIENT_CONTEXT *lpClientContext);
	void AcceptClients();

	// Control parameters
	long		m_NextConnectionID;
	WSADATA		m_wsaData;
	SOCKET		m_Listener;
	HANDLE		m_CompletionPort;
};

BOOL LoadConfiguration(BOOL FirstTimeLoad);
void CheckSocketTimeouts();
int	CurrentClients();
CLIENT_CONTEXT *CreateContext(SOCKET Socket,SOCKADDR_IN *ConnectionAddress);
void DeleteContext(CLIENT_CONTEXT *lpClientContext,BOOL bGraceful);
void ResetContext(CLIENT_CONTEXT *lpClientContext,BOOL ResetMailFrom);
DWORD WINAPI ListeningThread(LPVOID WorkContext);
DWORD WINAPI WorkerThread(LPVOID WorkContext);
void CheckForCriticalError(CLIENT_CONTEXT *lpClientContext);
void CheckSocketError(CLIENT_CONTEXT *lpClientContext);
void CloseClient(CLIENT_CONTEXT *lpClientContext,BOOL bGraceful);
int GetCommand(char *Data);
BOOL CommandLenError(int Command,char *Data);
BOOL ValidAddress(char *Address);
BOOL LocalAddress(char *Address,char *ConnectionAddress);
BOOL WhiteListIP(char *ConnectionAddress);
int SendHelp(CLIENT_CONTEXT *lpClientContext);
char *SearchAndReplace(char *InputBuffer,char *SearchFor,char *ReplaceWith,int *ReplacementCount);
int SendData(CLIENT_CONTEXT *lpClientContext,char *SendString,int StringLength);
BOOL ProcessFilter(CLIENT_CONTEXT *lpClientContext);
int ExtractHeaderElement(char *Source,int SourceSize,char *Item,int MaxItemSize,char *Value,int MaxValueSize,BOOL *AllSpaces);
int ExtractBodyLine(char *Source,int SourceSize,char *BodyLine,int MaxSize,BOOL *AllSpaces);
void TranslateString(char *Source);
void MimeDecodePrepare();
void MimeDecodeLine(char *Source,int Base);
void HexDecodeLine(char *Source);
void TranslateEncodedChars(CLIENT_CONTEXT *lpClientContext,char *Source);
void TranslateAnnotatedChars(char *Source);
void ExtractAddress(char *MailAddress,char *Storage,int MaxStorageSize,BOOL MailFromAddress);
void ReverseResolveAddress(CLIENT_CONTEXT *lpClientContext,char *MailAddress);
BOOL AggressiveResolveAddress(CLIENT_CONTEXT *lpClientContext,char *Address,BYTE *AddressList);
void CheckIPFilter(CLIENT_CONTEXT *lpClientContext);
void CheckDomainFilter(CLIENT_CONTEXT *lpClientContext,char *MailAddress,BOOL *SuspectDomain,int *SuspectResult,int BlackListSub);
void CheckKeywordFilter(CLIENT_CONTEXT *lpClientContext,char *Source,BOOL SubjectLine,BOOL FromField);
void CheckWhiteListRecipients(CLIENT_CONTEXT *lpClientContext,char *RecipientAddress,int RecipientPosition);
void CheckSuspectRecipients(CLIENT_CONTEXT *lpClientContext,char *RecipientAddress);
void CheckOutbreakFilter(CLIENT_CONTEXT *lpClientContext);
void RecordOutbreakTracking(CLIENT_CONTEXT *lpClientContext,char BlackListResult);
void RecordIPTracking(CLIENT_CONTEXT *lpClientContext);
void RecordDomainTracking(CLIENT_CONTEXT *lpClientContext);
BOOL FindString(char *Source,char *ToFind,int SearchType);
BOOL RemoveHTMLLinkSpace(CLIENT_CONTEXT *lpClientContext,char *Source);
BOOL RemoveExtraSpace(CLIENT_CONTEXT *lpClientContext,char *Source,BOOL CheckHTMLLinks,BOOL IPWhiteList);
BOOL SendToTurfDir(CLIENT_CONTEXT *lpClientContext,int BLType);
BOOL ConnectToSmartHost(CLIENT_CONTEXT *lpClientContext,int RetryDelay);
BOOL ForwardToSmartHost(CLIENT_CONTEXT *lpClientContext,BOOL BLForward,BOOL OnlyToWhiteRecipient);
BOOL SendBounceMessage(CLIENT_CONTEXT *lpClientContext,char *ErrorReport);
BOOL ReceiveSMTPResult(CLIENT_CONTEXT *lpClientContext,SOCKET HostSocket,char *Buffer,int BufferSize,char *ExpectedResult,char *LogEvent);
BOOL ConvertIPString(char *String,int *Num1,int *Num2,int *Num3,int *Num4);
void UpdateLogFile(char *Address,char *Source,char *String);
void FlushLogBuffers();
void LoadLocalDomainsFile();
void EmptyLocalDomainsFile();
void LoadDomainFilterFile();
void EmptyDomainFilterFile();
void LoadKeywordFilterFile();
void EmptyKeywordFilterFile();
void SortOutbreakFile(CLIENT_CONTEXT *lpClientContext = NULL);
void EmptyOutbreakFile();
void LoadTrackingLogFile(CLIENT_CONTEXT *lpClientContext = NULL);
void SaveTrackingLogFile(CLIENT_CONTEXT *lpClientContext = NULL);
void SortTrackingLogFile(CLIENT_CONTEXT *lpClientContext = NULL);
void EmptyTrackingLogFile();
BOOL IPInSubnet(int IPNum1,int IPNum2,int IPNum3,int IPNum4,int SubNum1,int SubNum2,int SubNum3,int SubNum4,int CheckIPNum1,int CheckIPNum2,int CheckIPNum3,int CheckIPNum4);
char *BuildDateString(char *Buffer,int BufferSize);
void YieldControl();
BOOL ContinueProcess(CLIENT_CONTEXT *lpClientContext,BOOL Phase1);
BOOL ConnectToDatabase(CLIENT_CONTEXT *lpClientContext);
void DisconnectFromDatabase(CLIENT_CONTEXT *lpClientContext);
BOOL ConnectStatement(CLIENT_CONTEXT *lpClientContext,char *CommandString);
void DisconnectStatement(CLIENT_CONTEXT *lpClientContext);
void DatabaseError(CLIENT_CONTEXT *lpClientContext);
char *GetConnectionTag(CLIENT_CONTEXT *lpClientContext);
void InvalidParameterHandler(const wchar_t *Expression,const wchar_t *Function,const wchar_t *File,unsigned int Line,uintptr_t pReserved);
void *AllocateBlock(int Size,BOOL TemporaryStorage);
void ReleaseBlock(void *Ptr,int Size);
void ReleaseAllMemory();
DWORD SocketError(CLIENT_CONTEXT *lpClientContext);
void MyTestFunction(CLIENT_CONTEXT *lpClientContext,char *TagLine);
