include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "wb.mm"
include "2re.mm"
include "2pos.mm"
include "gt0div.mm"
include "mp3an23.mm"

theorem halfpos2
  let cA: class A


  assert |- ( A e. RR -> ( 0 < A <-> 0 < ( A / 2 ) ) )

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
    clt
    wbr
    cc0
    cA
    c2
    cdiv
    co
    clt
    wbr
    wb
    2re
    2pos
    cA
    c2
    gt0div
    mp3an23
end
