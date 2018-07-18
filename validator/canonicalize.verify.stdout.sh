RUN_DIR=$1
STDOUT_FILE=$2

sed -i "s|$RUN_DIR|<beep>|g" $STDOUT_FILE
sed -i 's/([0-9]\+,[0-9-]\+)/(<beep>,<beep>)/g' $STDOUT_FILE
