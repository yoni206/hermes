unzip:
	#-o is for "override
	unzip -o solvers/\*.zip -d solvers
	#eliminate space
	mv "solvers/Yices 2.6.2" solvers/Yices_2.6.2

sed:
	chmod 755 subs.sh
	./subs.sh

clean:
	rm -rf `find solvers -maxdepth 1 -type d | grep "/"`
