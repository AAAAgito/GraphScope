import csv
from fileinput import filename
# files = ["Person", "Forum", "comment", "Post"]
# for filename in files:
#     reader = csv.reader(open('test_data//'+filename+'_0_0.csv',"r", encoding="utf-8"))
#     out = open(filename+'_0_0.csv', "a")
#     writer = csv.writer(out)
#     for i in reader:
#         i[0]=i[0].replace('\"',"")
#         idx = i[0].find('|')
#         idx2 = i[0].find('|',30)
#         info = i[0][:idx+1]
#         info2 = i[0][int(idx+1): int(idx2)+1]
#         res = info2+info+i[0][idx2+1::]
#         print(res)
#         writer.writerow([str(res)])

files = ["Person_hasInterest_Tag", "Person_isLocatedIn_City", "Person_knows_Person", "Person_likes_Comment", "Person_likes_Post", "Person_studyAt_University", "Person_workAt_Company",
     "Post_hasCreator_Person", "Post_hasTag_Tag", "Post_isLocatedIn_Country",
    "Forum_containerOf_Post", "Forum_hasMember_Person", "Forum_hasModerator_Person", "Forum_hasTag_Tag", 
    "Comment_hasCreator_Person", "Comment_hasTag_Tag", "Comment_isLocatedIn_Country", "Comment_replyOf_Comment", "Comment_replyOf_Post"
    ]
for filename in files:
    reader = csv.reader(open('test_data//'+filename+'.csv',"r", encoding="utf-8"))
    out = open(filename+'.csv', "a")
    writer = csv.writer(out)
    for i in reader:
        i[0]=i[0].replace('\"',"")
        idx = i[0].find('|')
        idx2 = i[0].find('|',30)
        info = i[0][:idx+1]
        info2 = i[0][int(idx+1): int(idx2)+1]
        res = i[0][idx+1::]
        print(res)
        writer.writerow([str(res)])