include "ctb.mm"
include "wcel.mm"
include "ctg.mm"
include "cfv.mm"
include "ctop.mm"
include "cuni.mm"
include "wceq.mm"
include "ctopon.mm"
include "tgcl.mm"
include "unitg.mm"
include "eqcomd.mm"
include "istopon.mm"
include "sylanbrc.mm"

theorem tgtopon
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cJ: class J
  let cV: class V
  let cC: class C


  assert |- ( B e. TopBases -> ( topGen ` B ) e. ( TopOn ` U. B ) )

  proof
    cB
    ctb
    wcel
    #
    cB
    ctg
    cfv
    #
    ctop
    wcel
    cB
    cuni
    #
    @1
    cuni
    #
    wceq
    @1
    @2
    ctopon
    cfv
    wcel
    cB
    tgcl
    @0
    @3
    @2
    cB
    ctb
    unitg
    eqcomd
    @2
    @1
    istopon
    sylanbrc
end
