include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "leadd2.mm"
include "mp3an.mm"

theorem leadd2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume lt2.1: |- A e. RR
  assume lt2.2: |- B e. RR
  assume lt2.3: |- C e. RR


  assert |- ( A <_ B <-> ( C + A ) <_ ( C + B ) )

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
    cC
    cA
    caddc
    co
    cC
    cB
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
    leadd2
    mp3an
end
