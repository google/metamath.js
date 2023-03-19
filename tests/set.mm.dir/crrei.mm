include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cre.mm"
include "cfv.mm"
include "wceq.mm"
include "crre.mm"
include "mp2an.mm"

theorem crrei
  let cA: class A
  let cB: class B
  assume crre.1: |- A e. RR
  assume crre.2: |- B e. RR


  assert |- ( Re ` ( A + ( _i x. B ) ) ) = A

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
    cre
    cfv
    cA
    wceq
    crre.1
    crre.2
    cA
    cB
    crre
    mp2an
end
