include "ctps.mm"
include "wcel.mm"
include "ctopon.mm"
include "cfv.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "istps.mm"
include "istopon.mm"
include "bitri.mm"

theorem istps2
  let cA: class A
  let cJ: class J
  let cK: class K
  let vf: setvar f
  assume istps.a: |- A = ( Base ` K )
  assume istps.j: |- J = ( TopOpen ` K )


  assert |- ( K e. TopSp <-> ( J e. Top /\ A = U. J ) )

  proof
    cK
    ctps
    wcel
    cJ
    cA
    ctopon
    cfv
    wcel
    cJ
    ctop
    wcel
    cA
    cJ
    cuni
    wceq
    wa
    cA
    cJ
    cK
    istps.a
    istps.j
    istps
    cA
    cJ
    istopon
    bitri
end
