include "cr.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "readdcl.mm"
include "mp2an.mm"

theorem readdcli
  param cA: class A
  param cB: class B
  assume recni.1: |- A e. RR
  assume axri.2: |- B e. RR


  assert |- ( A + B ) e. RR

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    caddc
    co
    cr
    wcel
    recni.1
    axri.2
    cA
    cB
    readdcl
    mp2an
end
