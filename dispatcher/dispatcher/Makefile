all: sed

sed: unzip
	#add the real path in each solver script
	chmod 755 subs.sh
	./subs.sh

unzip: clean
	#create all solver directories
	#-o is for "override
	unzip -o solvers/comp/\*.zip -d solvers/comp/
	#eliminate space
	mv "solvers/comp/Yices 2.6.2" solvers/comp/Yices_2.6.2

clean:
	#remove all solver directories
	rm -rf `find solvers/comp/ -maxdepth 1 -type d | grep -v comp/$`
