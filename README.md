# SpamHater notes:
SpamHater is a Windows service application that was originally written in 2003 solely authored and updated by Michael Read to manage anywhere from 300,000 to 1 million emails a month over 15+ years.  SpamHater was created before spam filtering in e-mail was commonly done and the options available were very highly priced.  SpamHater was meant to be the primary SMTP server as defined by the domains DNS. This application is not an e-mail server, it simply downloads, scans and forwards e-mail messages. Once an e-mail is received and classified ‘not spam’ it is forwarded to the “SmartHost” a.k.a. the organizations e-mail server.  This readme document is a technical overview of operation.

# Features of note:
* SpamHater is a mutli-threaded application using CriticalSections to synchronize thread access to shared resources.  The code for the worker threads was not put into a class at the time of development, but it could be.
* WinSock is used to accept data from new connections and send data to a SmartHost.
* A majority of the code is located in SMTPctrl.cpp and SMTPctrl.h.  I used preprocessor directives so I could easily add and remove code for short term debugging tasks.
* All connection activity is saved in log files (samples in the “logs” directory) that are regularly cleared out based on their age.
* SpamHater will monitoring changes made to configuration files and reload them without a need to restart the service. 
* At the top of each config text file there is a legend describing how to add and change entries.
* Used reverse resolution to verify the source domain claimed. 
* SpamHater has several new SMTP commands for administrative use.  These are described in the “instructions.txt” file.  Administrators can telnet to the app, monitor what is happening, and issue commands.
* New spam sources are tracked in a tracking log and saved to a “tracking.txt” file.  It counts how much spam is coming from each source so big offenders can be added to the config files to black list.
* Outside spam tracking sources called ‘DNS Black Lists’ were also used to help block new sources of spam.
* Known methods of decoding were used to reduce each e-mail down to basic ASCII characters for easy keyword searching.  Methods include MIME decoding, HTML character decoding, HTML HEX decoding, and annotated characters translated to ASCII equivalent.
* SMTP commands must be issued in a specific order.  The current state of the connection is tracked, as to what command the connection is expecting next, and what stage the filtration engine is at in its processing of each message.
* A count for each way the e-mails were black listed was maintained so administrators could track which methods were working best.  This could be seen with the STAT command from a telnet session:
    STAT
    ID=1, Time=0, Size=0, Error=0, State=HELO
    Process Time DHM=0:00:00, Min=0.00, Max=0.00, Avr=0.00
    Running DHM=0:00:00, Min Size=0, Max Size=0, Daily BL=0
    Total Messages=0, Black List=0 (0.00), White List=0 (0.00)
        BL Type: IP=0 (0.00), Conn=0, Dom=0, HTML=0, DNSBL=0
        Domain =0 (0.00), Address=0, Suspect=0, Reverse=0
        Keyword=0 (0.00), Subject=0, Body=0
        Format =0 (0.00), Address=0, Body=0
        Tag    =0 (0.00), Header=0, Admin Command=0
        Denied Connections=0, Messages Deleted=0, Outbreak Messages=0
    Tracking Log Size=0, Outbreak Log Size=0, Threads=48/1
* SpamHater was always a work in progress.  There are bits of code (like code to connect to an SQL database) that were not used, or no longer in use, but the code is still there just in case.

# Initialization:
There are several registry entries configuring basic operation. Three configuration text files in the “config” directory define configurable filters.  These files are loaded into memory and shared among all threads processing e-mail using several CriticalSections to control access to shared resources.  The application maintains an access count for shared resources and allows multiple threads to have access.  If one of the configuration files is manually changed, SpamHater will wait until the access count for the resource goes down to zero, then it will reload the configuration file and make that shared resource available to the threads again.

SpamHater creates a CompletionPort and creates the configured number of threads and associates them with the CompletionPort.  Then it uses WinSock to create a listening socket.  When a new connection is received, the application first allocates memory for a lpClientContext, which follows the connection through its life cycle and is the only structure unique about each connection.  All the threads use the same function to process their e-mail message.  Then SpamHater checks if the connection should be denied. Denial is determined by the configuration files, or if there are too many connections, from the same source.  Once it passes initial screening, the newly connected socket (with associated lpClientContext) is associated with the CompletionPort and one of the threads finishes processing the message.

# Operation:
The first thing the worker thread does is accept all the data being transmitted on the socket and saves it to a text file in a temp folder.  The content of the file is not touched.  The data is loaded into allocated memory which is tracked by the lpClientContext.  The thread will do what is necessary to decode, translate and analyze each part of the e-mail message (including the SMTP header), and compare the results to the shared configuration files.  If an e-mail is not blacklisted, then the temporary copy of the e-mail is used to send it to the SmartHost.  Otherwise, the file is moved to the “TurfDir” folder.  If an e-mail is mistakenly black listed, then it can be found and manually forwarded from the “TurfDir” folder.

# Clean up:
When processing is done for an lpClientContext it gets flagged for deletion.  The function used to perform trash collection is called CheckSocketTimeouts().

SpamHater stayed in service, with several updates along the way, for 15+ years and processed a very high volume of e-mails every day.  Detailed documentation about installation, configuration and operation is in the “instructions.txt” file.  
