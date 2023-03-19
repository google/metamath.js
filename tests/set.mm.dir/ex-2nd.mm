include "c3.mm"
include "c4.mm"
include "cr.mm"
include "3re.mm"
include "elexi.mm"
include "4re.mm"
include "op2nd.mm"

theorem ex-2nd



  assert |- ( 2nd ` <. 3 , 4 >. ) = 4

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
    op2nd
end
