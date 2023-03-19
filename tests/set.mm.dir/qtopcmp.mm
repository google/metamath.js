include "ccmp.mm"
include "cmptop.mm"
include "cqtop.mm"
include "co.mm"
include "cuni.mm"
include "eqid.mm"
include "cncmp.mm"
include "qtopcmplem.mm"

theorem qtopcmp
  let cF: class F
  let cJ: class J
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cY: class Y
  assume qtopcmp.1: |- X = U. J


  assert |- ( ( J e. Comp /\ F Fn X ) -> ( J qTop F ) e. Comp )

  proof
    ccmp
    cF
    cJ
    cX
    qtopcmp.1
    cJ
    cmptop
    cF
    cJ
    cJ
    cF
    cqtop
    co
    #
    cX
    @0
    cuni
    #
    @1
    eqid
    cncmp
    qtopcmplem
end
