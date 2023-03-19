include "cr.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "remulcl.mm"
include "mp2an.mm"

theorem remulcli
  let cA: class A
  let cB: class B
  assume recni.1: |- A e. RR
  assume axri.2: |- B e. RR


  assert |- ( A x. B ) e. RR

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cmul
    co
    cr
    wcel
    recni.1
    axri.2
    cA
    cB
    remulcl
    mp2an
end
