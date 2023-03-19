include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "leadd1.mm"
include "mp3an.mm"

theorem leadd1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR
  assume lt2.3: |- C e. RR


  assert |- ( A <_ B <-> ( A + C ) <_ ( B + C ) )

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
    cle
    wbr
    cA
    cC
    caddc
    co
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
    leadd1
    mp3an
end
