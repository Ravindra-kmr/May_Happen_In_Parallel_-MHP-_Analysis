**************Check ParTACOJava compliant Programs**************
Each test-case has to be a valid Java program. To keep our lives simple, we will stick to a simplified Java variant called ParTACoJava (http://www.cse.iitm.ac.in/~krishna/cs6235/subsets.html).

To ensure that your code is TACoJava compilant, do the following two simple tests:

- Check that the program is a valid Java program (using javac + java, for example).

- Check that the program  has valid TACoJava syntax.

    Download the tacojava grammar (say, to a directory called taco)
    Install javacc (https://javacc.github.io/javacc/)
    Run the following commands :
        javacc partacojava.jj
        javac TACoSyntaxChecker.java ## TACoSyntaxChecker.java is attached.
        ## Say you want to check if Factorial.java has valid TACoJava syntax:
        java TACoSyntaxChecker < Factorial.java 
