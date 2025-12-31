'''Python source designed to demonstrate '''
'''the use of python embedding'''

import sys
import os
import time
import mmap

INDATAFILENAME = '/testSharedmemory1'
LENGTHDATAMAP = 1024

class MMAPShmem:
    def run(self):
	mWrites = 20
        inDataFile = open(INDATAFILENAME, 'r+')
        print 'inDataFile size: ',  os.path.getsize(INDATAFILENAME),  'MMAP size: ', LENGTHDATAMAP
        inDataNo = inDataFile.fileno() 
        
        inDataMap = mmap.mmap(inDataNo, LENGTHDATAMAP, 
                              access=mmap.ACCESS_WRITE) 
        inDataMap.seek(0)    # simple test of validity
    
        # write something into the mapped file
        x = 567
        inDataMap.write('%d' %x + '\n')

        for i in range(mWrites):
            # read out from the file to verify
            inDataMap.seek(0)
            y = inDataMap.readline()
            print 'Python thread read from MMAP:', y 
            inDataMap.seek(0)
            inDataMap.write('%d' %x + '\n')
            print 'Python thread write back to MMAP:', x 
            time.sleep(1)

        inDataFile.close()

mmsh = MMAPShmem()
mmsh.run()
