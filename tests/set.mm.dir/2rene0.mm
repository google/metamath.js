include "c2.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "2re.mm"
include "2ne0.mm"
include "pm3.2i.mm"

theorem 2rene0



  assert |- ( 2 e. RR /\ 2 =/= 0 )

  proof
    c2
    cr
    wcel
    c2
    cc0
    wne
    2re
    2ne0
    pm3.2i
end
