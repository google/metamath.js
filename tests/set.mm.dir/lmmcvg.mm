include "cv.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "crp.mm"
include "cc.mm"
include "cpm.mm"
include "clm.mm"
include "lmmbr3.mm"
include "mpbid.mm"
include "simp3d.mm"
include "wceq.mm"
include "breq2.mm"
include "3anbi3d.mm"
include "rexralbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "wi.mm"
include "uztrn2.mm"
include "3simpc.mm"
include "eleq1d.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "syl5ib.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"

theorem lmmcvg
  let wph: wff ph
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume lmmbr.2: |- J = ( MetOpen ` D )
  assume lmmbr.3: |- ( ph -> D e. ( *Met ` X ) )
  assume lmmbr3.5: |- Z = ( ZZ>= ` M )
  assume lmmbr3.6: |- ( ph -> M e. ZZ )
  assume lmmbrf.7: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = A )
  assume lmmcvg.8: |- ( ph -> F ( ~~>t ` J ) P )
  assume lmmcvg.9: |- ( ph -> R e. RR+ )

  disjoint j k
  disjoint D j
  disjoint D k
  disjoint F j
  disjoint F k
  disjoint P j
  disjoint P k
  disjoint X j
  disjoint X k
  disjoint M j
  disjoint j ph
  disjoint k ph
  disjoint R j
  disjoint R k
  disjoint Z j
  disjoint Z k
  disjoint j u
  disjoint j x
  disjoint j y
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint u x
  disjoint u y
  disjoint D u
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint P u
  disjoint P x
  disjoint P y
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint J u
  disjoint J x
  disjoint J y
  disjoint ph u
  disjoint ph x
  disjoint R x
  disjoint Z x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( A e. X /\ ( A D P ) < R ) )

  proof
    wph
    vk
    cv
    #
    cF
    cdm
    wcel
    #
    @0
    cF
    cfv
    #
    cX
    wcel
    #
    @2
    cP
    cD
    co
    #
    cR
    clt
    wbr
    #
    w3a
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    cA
    cX
    wcel
    #
    cA
    cP
    cD
    co
    #
    cR
    clt
    wbr
    #
    wa
    #
    vk
    @8
    wral
    #
    vj
    cZ
    wrex
    wph
    cR
    crp
    wcel
    @1
    @3
    @4
    vx
    cv
    #
    clt
    wbr
    #
    w3a
    #
    vk
    @8
    wral
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @10
    lmmcvg.9
    wph
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    cP
    cX
    wcel
    #
    @20
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    @21
    @22
    @20
    w3a
    lmmcvg.8
    wph
    vx
    cD
    cP
    vj
    vk
    cF
    cJ
    cM
    cX
    cZ
    lmmbr.2
    lmmbr.3
    lmmbr3.5
    lmmbr3.6
    lmmbr3
    mpbid
    simp3d
    @19
    @10
    vx
    cR
    crp
    @16
    cR
    wceq
    #
    @18
    @6
    vj
    vk
    cZ
    @8
    @23
    @17
    @5
    @1
    @3
    @16
    cR
    @4
    clt
    breq2
    3anbi3d
    rexralbidv
    rspcv
    sylc
    wph
    @9
    @15
    vj
    cZ
    wph
    @7
    cZ
    wcel
    #
    wa
    @6
    @14
    vk
    @8
    wph
    @24
    @0
    @8
    wcel
    #
    @6
    @14
    wi
    #
    @24
    @25
    wa
    wph
    @0
    cZ
    wcel
    #
    @26
    cM
    @0
    @7
    cZ
    lmmbr3.5
    uztrn2
    @6
    @3
    @5
    wa
    wph
    @27
    wa
    #
    @14
    @1
    @3
    @5
    3simpc
    @28
    @3
    @11
    @5
    @13
    @28
    @2
    cA
    cX
    lmmbrf.7
    eleq1d
    @28
    @4
    @12
    cR
    clt
    @28
    @2
    cA
    cP
    cD
    lmmbrf.7
    oveq1d
    breq1d
    anbi12d
    syl5ib
    sylan2
    anassrs
    ralimdva
    reximdva
    mpd
end
