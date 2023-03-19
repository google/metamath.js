include "ctps.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "cbs.mm"
include "cfv.mm"
include "eqcomi.mm"
include "ctopn.mm"
include "istps2.mm"
include "mpbir2an.mm"

theorem istpsi
  let cA: class A
  let cJ: class J
  let cK: class K
  assume istpsi.b: |- ( Base ` K ) = A
  assume istpsi.j: |- ( TopOpen ` K ) = J
  assume istpsi.1: |- A = U. J
  assume istpsi.2: |- J e. Top


  assert |- K e. TopSp

  proof
    cK
    ctps
    wcel
    cJ
    ctop
    wcel
    cA
    cJ
    cuni
    wceq
    istpsi.2
    istpsi.1
    cA
    cJ
    cK
    cK
    cbs
    cfv
    cA
    istpsi.b
    eqcomi
    cK
    ctopn
    cfv
    cJ
    istpsi.j
    eqcomi
    istps2
    mpbir2an
end
