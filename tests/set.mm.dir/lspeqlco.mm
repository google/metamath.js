include "clmod.mm"
include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "clinco.mm"
include "co.mm"
include "clspn.mm"
include "cfv.mm"
include "lcosslsp.mm"
include "lspsslco.mm"
include "eqssd.mm"

theorem lspeqlco
  let cB: class B
  let cM: class M
  let cV: class V
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume lspeqvlco.b: |- B = ( Base ` M )


  assert |- ( ( M e. LMod /\ V e. ~P B ) -> ( M LinCo V ) = ( ( LSpan ` M ) ` V ) )

  proof
    cM
    clmod
    wcel
    cV
    cB
    cpw
    wcel
    wa
    cM
    cV
    clinco
    co
    cV
    cM
    clspn
    cfv
    cfv
    cB
    cM
    cV
    lspeqvlco.b
    lcosslsp
    cB
    cM
    cV
    lspeqvlco.b
    lspsslco
    eqssd
end
