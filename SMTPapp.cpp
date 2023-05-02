// SMTPApp.cpp
//
// This is the main program file containing the entry point.

#include "SMTPApp.h"
#include <sqlext.h>
#include "SMTPCtrl.h"

int main(int argc,char *argv[])
{
    // Create the service object
    CSMTPControl		SMTPControl;

    // Parse for standard arguments (install, uninstall, version etc.)
    if (!SMTPControl.ParseStandardArgs(argc,argv))
	{
        // Didn't find any standard args so start the service
        // Uncomment the DebugBreak line below to enter the debugger
        // when the service is started.
        //DebugBreak();
        SMTPControl.StartService();
    }

    // When we get here, the service has been stopped
    return SMTPControl.m_Status.dwWin32ExitCode;
}
