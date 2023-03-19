include "crngh.mm"
include "co.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "crng.mm"
include "wa.mm"
include "cghm.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "isrnghm.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc2va.mm"
include "expcom.mm"
include "ad2antll.mm"
include "sylbi.mm"
include "3impib.mm"

theorem rnghmmul
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume rnghmmul.x: |- X = ( Base ` R )
  assume rnghmmul.m: |- .x. = ( .r ` R )
  assume rnghmmul.n: |- .X. = ( .r ` S )


  assert |- ( ( F e. ( R RngHomo S ) /\ A e. X /\ B e. X ) -> ( F ` ( A .x. B ) ) = ( ( F ` A ) .X. ( F ` B ) ) )

  proof
    cF
    cR
    cS
    crngh
    co
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    c.x
    co
    #
    cF
    cfv
    #
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    c.xp
    co
    #
    wceq
    #
    @0
    cR
    crng
    wcel
    cS
    crng
    wcel
    wa
    #
    cF
    cR
    cS
    cghm
    co
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    cF
    cfv
    #
    @11
    cF
    cfv
    #
    @12
    cF
    cfv
    #
    c.xp
    co
    #
    wceq
    #
    vy
    cX
    wral
    vx
    cX
    wral
    #
    wa
    wa
    @1
    @2
    wa
    #
    @8
    wi
    #
    vx
    vy
    cX
    cR
    cS
    c.x
    cF
    c.xp
    rnghmmul.x
    rnghmmul.m
    rnghmmul.n
    isrnghm
    @19
    @21
    @9
    @10
    @20
    @19
    @8
    @18
    @8
    cA
    @12
    c.x
    co
    #
    cF
    cfv
    #
    @5
    @16
    c.xp
    co
    #
    wceq
    vx
    vy
    cA
    cB
    cX
    cX
    @11
    cA
    wceq
    #
    @14
    @23
    @17
    @24
    @25
    @13
    @22
    cF
    @11
    cA
    @12
    c.x
    oveq1
    fveq2d
    @25
    @15
    @5
    @16
    c.xp
    @11
    cA
    cF
    fveq2
    oveq1d
    eqeq12d
    @12
    cB
    wceq
    #
    @23
    @4
    @24
    @7
    @26
    @22
    @3
    cF
    @12
    cB
    cA
    c.x
    oveq2
    fveq2d
    @26
    @16
    @6
    @5
    c.xp
    @12
    cB
    cF
    fveq2
    oveq2d
    eqeq12d
    rspc2va
    expcom
    ad2antll
    sylbi
    3impib
end
