include "c2.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "pm3.2i.mm"

theorem 2cnne0



  assert |- ( 2 e. CC /\ 2 =/= 0 )

  proof
    c2
    cc
    wcel
    c2
    cc0
    wne
    2cn
    2ne0
    pm3.2i
end
