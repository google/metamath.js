include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cim.mm"
include "cfv.mm"
include "wceq.mm"
include "crim.mm"
include "mp2an.mm"

theorem crimi
  let cA: class A
  let cB: class B
  assume crre.1: |- A e. RR
  assume crre.2: |- B e. RR


  assert |- ( Im ` ( A + ( _i x. B ) ) ) = B

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    ci
    cB
    cmul
    co
    caddc
    co
    cim
    cfv
    cB
    wceq
    crre.1
    crre.2
    cA
    cB
    crim
    mp2an
end
