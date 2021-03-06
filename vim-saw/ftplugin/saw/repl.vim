function! DeleteBlank()
  keepp %g/^\s*\n/d
  keepp %g/^\n/d
  keepp %g/^\s*\/\/.*\n/d
  keepp %s/\/\/.*\n/\r/eg " remove end-of-line comments
endfunction

function! CreateSplit()
  normal! `<v`>y
  split __scratch__
  setlocal buftype=nofile
  setlocal bufhidden=delete
  normal! p
  call DeleteBlank()
endfunction

function! Join_and_copy(type)
  if a:type ==# 'V' " only do stuff in line-wise visual mode
    call CreateSplit()
    " join lines and yank:
    normal! ggVGJyy
    q " close scratch split
  endif
endfunction

function! Copy(type)
  if a:type ==# 'V' " only do stuff in line-wise visual mode
    call CreateSplit()
    %s/\n/\\\r/g " add backslash at end of lines
    " remove last line (is blank)
    normal! Gdd
    " remove backslash at end of (new) last line:
    normal! G$x
    " yank:
    normal! ggVGy
    q " close scratch split
  endif
endfunction
