all: sed

sed: unzip
	#add the real path in each solver script
	chmod 755 subs.sh
	./subs.sh

unzip: clean
	#create all solver directories
	#-o is for "override
	unzip -o solvers/\*.zip -d solvers
	#eliminate space
	mv "solvers/Yices 2.6.2" solvers/Yices_2.6.2

clean:
	#remove all solver directories
	rm -rf `find solvers -maxdepth 1 -type d | grep "/"`
