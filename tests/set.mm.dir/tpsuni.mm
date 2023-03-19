include "ctps.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "istps2.mm"
include "simprbi.mm"

theorem tpsuni
  let cA: class A
  let cJ: class J
  let cK: class K
  let vf: setvar f
  assume istps.a: |- A = ( Base ` K )
  assume istps.j: |- J = ( TopOpen ` K )


  assert |- ( K e. TopSp -> A = U. J )

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
    cA
    cJ
    cK
    istps.a
    istps.j
    istps2
    simprbi
end
