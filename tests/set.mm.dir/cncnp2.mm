include "c0.mm"
include "wne.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "ccnp.mm"
include "cfv.mm"
include "wral.mm"
include "ctopon.mm"
include "wa.mm"
include "wf.mm"
include "ctop.mm"
include "cntop1.mm"
include "toptopon.mm"
include "sylib.mm"
include "cntop2.mm"
include "cnf.mm"
include "jca31.mm"
include "adantl.mm"
include "wrex.mm"
include "r19.2z.mm"
include "cnptop1.mm"
include "cnptop2.mm"
include "cnpf.mm"
include "rexlimivw.mm"
include "syl.mm"
include "cncnp.mm"
include "baibd.mm"
include "pm5.21nd.mm"

theorem cncnp2
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vy: setvar y
  assume cncnp.1: |- X = U. J
  assume cncnp.2: |- Y = U. K

  disjoint F x
  disjoint J x
  disjoint K x
  disjoint X x
  disjoint Y x
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint x y
  disjoint F y
  disjoint J u
  disjoint J y
  disjoint K u
  disjoint K y
  disjoint X u
  disjoint X y
  disjoint Y u
  disjoint Y y
  assert |- ( X =/= (/) -> ( F e. ( J Cn K ) <-> A. x e. X F e. ( ( J CnP K ) ` x ) ) )

  proof
    cX
    c0
    wne
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cF
    vx
    cv
    #
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    vx
    cX
    wral
    #
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
    wa
    #
    cX
    cY
    cF
    wf
    #
    wa
    #
    @1
    @9
    @0
    @1
    @5
    @6
    @8
    @1
    cJ
    ctop
    wcel
    #
    @5
    cF
    cJ
    cK
    cntop1
    cJ
    cX
    cncnp.1
    toptopon
    #
    sylib
    @1
    cK
    ctop
    wcel
    #
    @6
    cF
    cJ
    cK
    cntop2
    cK
    cY
    cncnp.2
    toptopon
    #
    sylib
    cF
    cJ
    cK
    cX
    cY
    cncnp.1
    cncnp.2
    cnf
    jca31
    adantl
    @0
    @4
    wa
    @3
    vx
    cX
    wrex
    @9
    @3
    vx
    cX
    r19.2z
    @3
    @9
    vx
    cX
    @3
    @5
    @6
    @8
    @3
    @10
    @5
    @2
    cF
    cJ
    cK
    cnptop1
    @11
    sylib
    @3
    @12
    @6
    @2
    cF
    cJ
    cK
    cnptop2
    @13
    sylib
    @2
    cF
    cJ
    cK
    cX
    cY
    cncnp.1
    cncnp.2
    cnpf
    jca31
    rexlimivw
    syl
    @7
    @1
    @8
    @4
    vx
    cF
    cJ
    cK
    cX
    cY
    cncnp
    baibd
    pm5.21nd
end
