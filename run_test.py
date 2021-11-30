import os
import subprocess
import pathlib 
from pathlib import Path



folder = pathlib.Path(__file__).parent.resolve()
#input for caf controllability solver file 
asp_program = Path(folder.__str__() , "chain_asp_1.lp")

#creates result file if needed
if (not (os.path.exists(folder.__str__() + "test_result.csv"))):
	document = open(folder.__str__() + "test_result.csv", "w")	
	document.close

#loops though test files
for filename in os.listdir(Path(folder.__str__() , 'Test_instances')):
	with open(os.path.join(Path(folder.__str__() ,'Test_instances', filename))) as file:
		test_case = open(file.name,"r")
		#calls c api solver for controllability programs as a subprocess. to run skeptical the first input for the subprocess should be changed. after 100 seconds the subprocess is killed and Timeout is the result for an instance
		try:
			result = subprocess.run(["./cred_cont", "chain_asp_1.lp", test_case.name], capture_output=True, text=True, timeout=100)
			document = open("test_result.csv", "a")
			document.write(result.stdout + "\n")
			document.close
			print(result.stderr)
			test_case.close
		except subprocess.TimeoutExpired:
			document = open("test_result.csv", "a")
			document.write("Timeout" + "\n")
			document.close
			print("Timeout")
#all instances of the folder got run through
print("Done!")
