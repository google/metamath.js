include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "cmpt2.mm"
include "crn.mm"
include "clsm.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "simp11.mm"
include "simp12.mm"
include "elpwid.mm"
include "simp2.mm"
include "sseldd.mm"
include "simp13.mm"
include "simp3.mm"
include "syl12anc.mm"
include "mpt2eq3dva.mm"
include "rneqd.mm"
include "pweqd.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "3eqtr3d.mm"
include "cvv.mm"
include "eqid.mm"
include "lsmfval.mm"
include "syl.mm"
include "3eqtr4d.mm"

theorem lsmpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cK: class K
  let cL: class L
  let vt: setvar t
  let vu: setvar u
  assume lsmpropd.b1: |- ( ph -> B = ( Base ` K ) )
  assume lsmpropd.b2: |- ( ph -> B = ( Base ` L ) )
  assume lsmpropd.p: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` K ) y ) = ( x ( +g ` L ) y ) )
  assume lsmpropd.v1: |- ( ph -> K e. _V )
  assume lsmpropd.v2: |- ( ph -> L e. _V )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint ph x
  disjoint ph y
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint B t
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint K t
  disjoint K u
  disjoint L t
  disjoint L u
  disjoint ph t
  disjoint ph u
  assert |- ( ph -> ( LSSum ` K ) = ( LSSum ` L ) )

  proof
    wph
    vt
    vu
    cK
    cbs
    cfv
    #
    cpw
    #
    @1
    vx
    vy
    vt
    cv
    #
    vu
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cK
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    crn
    #
    cmpt2
    #
    vt
    vu
    cL
    cbs
    cfv
    #
    cpw
    #
    @12
    vx
    vy
    @2
    @3
    @4
    @5
    cL
    cplusg
    cfv
    #
    co
    #
    cmpt2
    #
    crn
    #
    cmpt2
    #
    cK
    clsm
    cfv
    #
    cL
    clsm
    cfv
    #
    wph
    vt
    vu
    cB
    cpw
    #
    @20
    @9
    cmpt2
    #
    vt
    vu
    @20
    @20
    @16
    cmpt2
    #
    @10
    @17
    wph
    vt
    vu
    @20
    @20
    @9
    @16
    wph
    @2
    @20
    wcel
    #
    @3
    @20
    wcel
    #
    w3a
    #
    @8
    @15
    @25
    vx
    vy
    @2
    @3
    @7
    @14
    @25
    @4
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    w3a
    #
    wph
    @4
    cB
    wcel
    @5
    cB
    wcel
    @7
    @14
    wceq
    wph
    @23
    @24
    @26
    @27
    simp11
    @28
    @2
    cB
    @4
    @28
    @2
    cB
    wph
    @23
    @24
    @26
    @27
    simp12
    elpwid
    @25
    @26
    @27
    simp2
    sseldd
    @28
    @3
    cB
    @5
    @28
    @3
    cB
    wph
    @23
    @24
    @26
    @27
    simp13
    elpwid
    @25
    @26
    @27
    simp3
    sseldd
    lsmpropd.p
    syl12anc
    mpt2eq3dva
    rneqd
    mpt2eq3dva
    wph
    @20
    @1
    wceq
    #
    @29
    @21
    @10
    wceq
    wph
    cB
    @0
    lsmpropd.b1
    pweqd
    #
    @30
    vt
    vu
    @20
    @20
    @1
    @1
    @9
    mpt2eq12
    syl2anc
    wph
    @20
    @12
    wceq
    #
    @31
    @22
    @17
    wceq
    wph
    cB
    @11
    lsmpropd.b2
    pweqd
    #
    @32
    vt
    vu
    @20
    @20
    @12
    @12
    @16
    mpt2eq12
    syl2anc
    3eqtr3d
    wph
    cK
    cvv
    wcel
    @18
    @10
    wceq
    lsmpropd.v1
    vx
    vy
    vu
    vt
    @0
    @6
    @18
    cK
    cvv
    @0
    eqid
    @6
    eqid
    @18
    eqid
    lsmfval
    syl
    wph
    cL
    cvv
    wcel
    @19
    @17
    wceq
    lsmpropd.v2
    vx
    vy
    vu
    vt
    @11
    @13
    @19
    cL
    cvv
    @11
    eqid
    @13
    eqid
    @19
    eqid
    lsmfval
    syl
    3eqtr4d
end
