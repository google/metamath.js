include "ccfil.mm"
include "cfv.mm"
include "cv.mm"
include "cfil.mm"
include "wcel.mm"
include "cbl.mm"
include "co.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "wa.mm"
include "cdiv.mm"
include "wi.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "rpdivcld.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "syl.mm"
include "wss.mm"
include "simpllr.mm"
include "cmopn.mm"
include "eqid.mm"
include "metss2lem.mm"
include "ancom2s.mm"
include "adantlr.mm"
include "anassrs.mm"
include "cxmt.mm"
include "cxr.mm"
include "cme.mm"
include "ad3antrrr.mm"
include "metxmet.mm"
include "rpxr.mm"
include "ad2antlr.mm"
include "blssm.mm"
include "syl3anc.mm"
include "filss.mm"
include "3exp2.mm"
include "com24.mm"
include "syl3c.mm"
include "reximdva.mm"
include "syld.mm"
include "ralrimdva.mm"
include "imdistanda.mm"
include "wb.mm"
include "iscfil3.mm"
include "3syl.mm"
include "3imtr4d.mm"
include "ssrdv.mm"

theorem equivcfil
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  let cD: class D
  let cR: class R
  let cX: class X
  let vf: setvar f
  let vk: setvar k
  let vr: setvar r
  let vs: setvar s
  assume equivcau.1: |- ( ph -> C e. ( Met ` X ) )
  assume equivcau.2: |- ( ph -> D e. ( Met ` X ) )
  assume equivcau.3: |- ( ph -> R e. RR+ )
  assume equivcau.4: |- ( ( ph /\ ( x e. X /\ y e. X ) ) -> ( x C y ) <_ ( R x. ( x D y ) ) )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint X x
  disjoint X y
  disjoint f k
  disjoint f r
  disjoint f x
  disjoint f y
  disjoint C f
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint C k
  disjoint r x
  disjoint r y
  disjoint C r
  disjoint f s
  disjoint D f
  disjoint k s
  disjoint D k
  disjoint r s
  disjoint D r
  disjoint s x
  disjoint s y
  disjoint D s
  disjoint f ph
  disjoint k ph
  disjoint ph r
  disjoint R k
  disjoint R s
  disjoint X f
  disjoint X k
  disjoint X r
  disjoint X s
  assert |- ( ph -> ( CauFil ` D ) C_ ( CauFil ` C ) )

  proof
    wph
    vf
    cD
    ccfil
    cfv
    #
    cC
    ccfil
    cfv
    #
    wph
    vf
    cv
    #
    cX
    cfil
    cfv
    wcel
    #
    vx
    cv
    #
    vs
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @2
    wcel
    #
    vx
    cX
    wrex
    #
    vs
    crp
    wral
    #
    wa
    #
    @3
    @4
    vr
    cv
    #
    cC
    cbl
    cfv
    co
    #
    @2
    wcel
    #
    vx
    cX
    wrex
    #
    vr
    crp
    wral
    #
    wa
    #
    @2
    @0
    wcel
    #
    @2
    @1
    wcel
    #
    wph
    @3
    @10
    @16
    wph
    @3
    wa
    #
    @10
    @15
    vr
    crp
    @20
    @12
    crp
    wcel
    #
    wa
    #
    @10
    @4
    @12
    cR
    cdiv
    co
    #
    @6
    co
    #
    @2
    wcel
    #
    vx
    cX
    wrex
    #
    @15
    @22
    @23
    crp
    wcel
    @10
    @26
    wi
    @22
    @12
    cR
    @20
    @21
    simpr
    wph
    cR
    crp
    wcel
    @3
    @21
    equivcau.3
    ad2antrr
    rpdivcld
    @9
    @26
    vs
    @23
    crp
    @5
    @23
    wceq
    #
    @8
    @25
    vx
    cX
    @27
    @7
    @24
    @2
    @5
    @23
    @4
    @6
    oveq2
    eleq1d
    rexbidv
    rspcv
    syl
    @22
    @25
    @14
    vx
    cX
    @22
    @4
    cX
    wcel
    #
    wa
    #
    @3
    @24
    @13
    wss
    #
    @13
    cX
    wss
    #
    @25
    @14
    wi
    wph
    @3
    @21
    @28
    simpllr
    @20
    @21
    @28
    @30
    wph
    @21
    @28
    wa
    @30
    @3
    wph
    @28
    @21
    @30
    wph
    vx
    vy
    cC
    cD
    cR
    @12
    cC
    cmopn
    cfv
    #
    cD
    cmopn
    cfv
    #
    cX
    @32
    eqid
    @33
    eqid
    equivcau.1
    equivcau.2
    equivcau.3
    equivcau.4
    metss2lem
    ancom2s
    adantlr
    anassrs
    @29
    cC
    cX
    cxmt
    cfv
    #
    wcel
    #
    @28
    @12
    cxr
    wcel
    #
    @31
    @29
    cC
    cX
    cme
    cfv
    #
    wcel
    #
    @35
    wph
    @38
    @3
    @21
    @28
    equivcau.1
    ad3antrrr
    cC
    cX
    metxmet
    #
    syl
    @22
    @28
    simpr
    @21
    @36
    @20
    @28
    @12
    rpxr
    ad2antlr
    cC
    @4
    @12
    cX
    blssm
    syl3anc
    @3
    @25
    @31
    @30
    @14
    @3
    @25
    @31
    @30
    @14
    @24
    @13
    @2
    cX
    filss
    3exp2
    com24
    syl3c
    reximdva
    syld
    ralrimdva
    imdistanda
    wph
    cD
    @37
    wcel
    cD
    @34
    wcel
    @18
    @11
    wb
    equivcau.2
    cD
    cX
    metxmet
    vx
    cD
    @2
    cX
    vs
    iscfil3
    3syl
    wph
    @38
    @35
    @19
    @17
    wb
    equivcau.1
    @39
    vx
    cC
    @2
    cX
    vr
    iscfil3
    3syl
    3imtr4d
    ssrdv
end
