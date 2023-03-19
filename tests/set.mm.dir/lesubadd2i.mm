include "cr.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "wb.mm"
include "lesubadd2.mm"
include "mp3an.mm"

theorem lesubadd2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR
  assume lt2.3: |- C e. RR


  assert |- ( ( A - B ) <_ C <-> A <_ ( B + C ) )

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
    cle
    wbr
    cA
    cB
    cC
    caddc
    co
    cle
    wbr
    wb
    lt2.1
    lt2.2
    lt2.3
    cA
    cB
    cC
    lesubadd2
    mp3an
end
