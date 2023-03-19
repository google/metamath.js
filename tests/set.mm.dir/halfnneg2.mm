include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "2re.mm"
include "2pos.mm"
include "ge0div.mm"
include "mp3an23.mm"

theorem halfnneg2
  let cA: class A


  assert |- ( A e. RR -> ( 0 <_ A <-> 0 <_ ( A / 2 ) ) )

  proof
    cA
    cr
    wcel
    c2
    cr
    wcel
    cc0
    c2
    clt
    wbr
    cc0
    cA
    cle
    wbr
    cc0
    cA
    c2
    cdiv
    co
    cle
    wbr
    wb
    2re
    2pos
    cA
    c2
    ge0div
    mp3an23
end
