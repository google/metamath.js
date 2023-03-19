include "cr.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "wb.mm"
include "ltsubadd2.mm"
include "mp3an.mm"

theorem ltsubadd2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR
  assume lt2.3: |- C e. RR


  assert |- ( ( A - B ) < C <-> A < ( B + C ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cC
    cr
    wcel
    cA
    cB
    cmin
    co
    cC
    clt
    wbr
    cA
    cB
    cC
    caddc
    co
    clt
    wbr
    wb
    lt2.1
    lt2.2
    lt2.3
    cA
    cB
    cC
    ltsubadd2
    mp3an
end
