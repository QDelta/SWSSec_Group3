from fileinput import filename
import idlelib.colorizer as idc
import idlelib.percolator as idp
import tkinter as tk
import tkinter.font as tf
import tkinter.messagebox as tm
import subprocess as subp
import re
from driver import analyze
# from PIL import Image, ImageTk

error_info = []
error_col = []


def get_content():  # 更新右侧display文本框的内容
    pos = 0

    for i in range(0, 200):
        tmp_start = str(i)+'.0'
        tmp_end = str(i)+'.200'
        cur = text.get(tmp_start, tmp_end)
        display.tag_add('tag_1', tmp_start)
        display.tag_config('tag_1', background='white', font=ft)

        
        if pos >= len(error_col):
            display.insert(tmp_start, cur+'\n', 'tag_1')
            continue
        if error_col[pos] == i:
            tmp_err = str(i)+'.0'
            display.tag_add('tag', tmp_err)  # 申明一个tag,在a位置使用
            display.tag_config('tag', background='pink',
                               font=ft)  # 设置tag即插入文字的大小,颜色等
            cur += '    < '+str(error_info[pos])+' >'
            pos += 1
            display.insert(tmp_err, cur+'\n', 'tag')
        else:
            display.insert(tmp_start, cur+'\n', 'tag_1')


def found_error():  # 如果我们找到了vulnerability，输出提示信息
    tm.showerror(title='Oops!', message=
        f':( , we found {len(error_col)} vulnerabilities!')


def all_is_well():  # 如果我们没有找到vulnerability，输出提示信息
    tm.showinfo(title='Congratulations', message=
        ';) , looks like there are no vulnerabilities!')


def tips():  # 提示信息框
    tm.showinfo(title='Enjoy it ;)', message='Instructions:\nEnter your code in the text box on the left side, then click process to check the vulnerability of it, the output will displayed on the right side.\n\n\nSystem made by NUS_SWS_DOTA_Group3\n      Hong Yun\n      Qin Jianxing\n      Qu Shaobo\n      Zhang Shuhao')


def compile_fail(msg):  # 检测是否有语法错误
    ans = ''
    for c in range(0, len(msg)):
        # msg[c]=msg[c].sub()
        if re.match('demo.c:\d+:\d+: error:', msg[c]):
            msg[c] = msg[c].replace('demo.c:', '')
            msg[c] = msg[c].replace(' error:', '')
            msg[c] = msg[c].replace(':', ',', 1)
            msg[c] = msg[c].replace(':', '):', 1)
            ans += ('('+msg[c])+'\n'
    # print(ans)
    if len(ans) > 0:
        display.tag_add('tag', 0.0) 
        display.tag_config('tag', background='pink',
                           font=ft)
        display.insert(0.0, 'Build Fail!\n\n'+ans, 'tag')
        tm.showerror(title='Oops!', message=
            ':( , we found some errors in your code!\nWe can\'t check its vulnerability until you fix these errors.')

    return ans


def coding_compile(coding):  # 利用gcc获取编译信息
    coding = "#define ASSUME(...)\nint *alloc(int);\nvoid print(int);\n" + coding
    filename = 'demo.c'
    with open(filename, 'w')as file:
        file.write(coding)
    compiler = 'gcc'
    options = ['-Werror', '-fsyntax-only']
    cur_cmd = subp.run([compiler] + options + [filename], capture_output=True)
    msg = cur_cmd.stderr
    return msg_process(str(msg, encoding="utf-8"))


def msg_process(msg):  # 处理gcc返回的编译信息
    msg_list = msg.split(sep='\n')
    return len(compile_fail(msg_list)) == 0


def content_update():  # 处理从左侧文本框text中读取的信息
    display.delete(1.0, 200.200)
    coding = text.get(1.0, 200.200)
    if not coding_compile(coding):
        return

    global error_info
    global error_col
    error_col, error_info=analyze(coding)
    get_content()

    if len(error_col) > 0:
        found_error()
    else:
        all_is_well()


def func_about():  # 下方about_bar
    tips()


def func_quit():  # 下方quit_bar
    tm.showinfo(title='Bye', message=('Thanks for using!\nBye then ;)'))
    root.destroy()




def welcome():
    welcome_page=tk.Tk()
    welcome_page.title('hello')
    welcome_page.geometry('1000x800')
    welcome_page.state('zoomed')
    poster = tk.PhotoImage(file="/img/poster.gif")
    imgLabel = tk.Label(welcome_page,image=poster)
    imgLabel.pack(side=tk.TOP)
    # load=Image.open("/img/poster.png")
    # poster=ImageTk.PhotoImage(load)
    # imgLabel=tk.Label(welcome_page,image=poster)
    # imgLabel.image=poster
    # imgLabel.pack(side=tk.TOP)
    # botm = tk.Button(
    #             text='Let\'s GO!',      # 显示在按钮上的文字
    #             width=15, height=1,
    #             command=welcome_page.destroy(),
    #             fg='red')     # 点击按钮式执行的命令
    # # b.grid(row=55,column=55)
    # botm.pack(side=tk.BOTTOM)
    # welcome_page.mainloop()



if __name__ == '__main__':

    # this will cause segfault!
    # welcome_page=tk.Tk()
    # welcome_page.destroy()
    # welcome()


    root = tk.Tk()
    root.title('Vulnerability Checker')
    root.geometry('500x800')
    root.state('zoomed')

    ft = tf.Font(family='Fixedsys', size=14)

    bt_frm = tk.Frame(root)
    bt_frm.pack(side=tk.BOTTOM)
    bt_frm['relief'] = 'groove'
    bt_frm['borderwidth'] = 0
    bt_frm['background'] = 'yellow'

    b = tk.Button(bt_frm,
                  text='Process',      # 显示在按钮上的文字
                  width=15, height=1,
                  command=content_update)     # 点击按钮式执行的命令
    # b.grid(row=55,column=55)
    b.pack(side=tk.LEFT)

    c = tk.Button(bt_frm,
                  text='About',      # 显示在按钮上的文字
                  width=15, height=1,
                  command=func_about,
                  fg='blue')     # 点击按钮式执行的命令
    # b.grid(row=55,column=55)
    c.pack(side=tk.LEFT)

    d = tk.Button(bt_frm,
                  text='Quit',      # 显示在按钮上的文字
                  width=15, height=1,
                  command=func_quit,
                  fg='red')     # 点击按钮式执行的命令
    # b.grid(row=55,column=55)
    d.pack(side=tk.LEFT)

    # 代码高亮
    text = tk.Text(root, font=ft)
    text.pack(fill=tk.BOTH, side=tk.LEFT)
    # text.grid(row=2,column=5)
    idc.color_config(text)
    text.focus_set()
    p = idp.Percolator(text)
    d = idc.ColorDelegator()
    p.insertfilter(d)

    display = tk.Text(root, font=ft)
    display.pack(fill=tk.BOTH, side=tk.RIGHT)
    # display.grid(row=2,column=110)
    idc.color_config(display)
    display.focus_set()
    p = idp.Percolator(display)
    d = idc.ColorDelegator()
    p.insertfilter(d)

    root.mainloop()