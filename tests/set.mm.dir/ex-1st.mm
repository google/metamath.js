include "c3.mm"
include "c4.mm"
include "cr.mm"
include "3re.mm"
include "elexi.mm"
include "4re.mm"
include "op1st.mm"

theorem ex-1st



  assert |- ( 1st ` <. 3 , 4 >. ) = 3

  proof
    c3
    c4
    c3
    cr
    3re
    elexi
    c4
    cr
    4re
    elexi
    op1st
end
