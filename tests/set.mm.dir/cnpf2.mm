include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ccnp.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "cuni.mm"
include "eqid.mm"
include "cnpf.mm"
include "toponuni.mm"
include "feq2d.mm"
include "feq3d.mm"
include "sylan9bb.mm"
include "syl5ibr.mm"
include "3impia.mm"

theorem cnpf2
  let cP: class P
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vx: setvar x


  assert |- ( ( J e. ( TopOn ` X ) /\ K e. ( TopOn ` Y ) /\ F e. ( ( J CnP K ) ` P ) ) -> F : X --> Y )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cF
    cP
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    cX
    cY
    cF
    wf
    #
    @2
    @3
    @0
    @1
    wa
    cJ
    cuni
    #
    cK
    cuni
    #
    cF
    wf
    #
    cP
    cF
    cJ
    cK
    @4
    @5
    @4
    eqid
    @5
    eqid
    cnpf
    @0
    @3
    @4
    cY
    cF
    wf
    @1
    @6
    @0
    cX
    @4
    cY
    cF
    cX
    cJ
    toponuni
    feq2d
    @1
    cY
    @5
    cF
    @4
    cY
    cK
    toponuni
    feq3d
    sylan9bb
    syl5ibr
    3impia
end
