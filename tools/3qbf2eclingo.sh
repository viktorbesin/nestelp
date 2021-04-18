for inst in `ls ../qbf_instances/*.qdimacs`
do
	../tools/3qbf2eclingo.py -c -i $inst -o $inst.elp
done

