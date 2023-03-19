include "cr.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "wb.mm"
include "ltaddsub.mm"
include "mp3an.mm"

theorem ltaddsubi
  let cA: class A
  let cB: class B
  let cC: class C
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR
  assume lt2.3: |- C e. RR


  assert |- ( ( A + B ) < C <-> A < ( C - B ) )

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
    caddc
    co
    cC
    clt
    wbr
    cA
    cC
    cB
    cmin
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
    ltaddsub
    mp3an
end
