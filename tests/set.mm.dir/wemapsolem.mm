include "cmap.mm"
include "co.mm"
include "wss.mm"
include "wpo.mm"
include "cvv.mm"
include "wcel.mm"
include "wor.mm"
include "sopo.mm"
include "syl.mm"
include "wemappo.mm"
include "syl3anc.mm"
include "poss.mm"
include "mpsyl.mm"
include "cv.mm"
include "wa.mm"
include "weq.mm"
include "wbr.mm"
include "wo.mm"
include "w3o.mm"
include "wn.mm"
include "wne.mm"
include "df-ne.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cdif.mm"
include "cdm.mm"
include "crab.mm"
include "wfn.mm"
include "wf.mm"
include "simprll.mm"
include "sseldi.mm"
include "elmapi.mm"
include "ffn.mm"
include "simprlr.mm"
include "fndmdif.mm"
include "syl2anc.mm"
include "eleq2d.mm"
include "nesym.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "notbid.mm"
include "syl5bb.mm"
include "elrab.mm"
include "syl6bb.mm"
include "imbi1d.mm"
include "impexp.mm"
include "con34b.mm"
include "imbi2i.mm"
include "bitr4i.mm"
include "ralbidv2.mm"
include "anbi12d.mm"
include "anass.mm"
include "rexbidv2.mm"
include "mpbid.mm"
include "ad2antrr.mm"
include "ffvelrnda.mm"
include "sotrieq.mm"
include "con2bid.mm"
include "biimprd.mm"
include "syl12anc.mm"
include "anim1d.mm"
include "reximdva.mm"
include "mpd.mm"
include "wb.mm"
include "vex.mm"
include "wemaplem1.mm"
include "mp2an.mm"
include "orbi12i.mm"
include "r19.43.mm"
include "andir.mm"
include "eqcom.mm"
include "ralbii.mm"
include "anbi2i.mm"
include "orbi2i.mm"
include "bitr2i.mm"
include "rexbii.mm"
include "3bitr2i.mm"
include "sylibr.mm"
include "expr.mm"
include "syl5bir.mm"
include "orrd.mm"
include "3orrot.mm"
include "3orass.mm"
include "sylib.mm"
include "issod.mm"

theorem wemapsolem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cX: class X
  let cP: class P
  let cQ: class Q
  let cZ: class Z
  assume wemapso.t: |- T = { <. x , y >. | E. z e. A ( ( x ` z ) S ( y ` z ) /\ A. w e. A ( w R z -> ( x ` w ) = ( y ` w ) ) ) }
  assume wemapsolem.1: |- U C_ ( B ^m A )
  assume wemapsolem.2: |- ( ph -> A e. _V )
  assume wemapsolem.3: |- ( ph -> R Or A )
  assume wemapsolem.4: |- ( ph -> S Or B )
  assume wemapsolem.5: |- ( ( ph /\ ( ( a e. U /\ b e. U ) /\ a =/= b ) ) -> E. c e. dom ( a \ b ) A. d e. dom ( a \ b ) -. d R c )

  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a x
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b x
  disjoint B b
  disjoint c d
  disjoint c x
  disjoint B c
  disjoint d x
  disjoint B d
  disjoint B x
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q d
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint Z c
  disjoint Z d
  disjoint Z x
  assert |- ( ph -> T Or U )

  proof
    wph
    va
    vb
    cU
    cT
    cU
    cB
    cA
    cmap
    co
    #
    wss
    wph
    @0
    cT
    wpo
    #
    cU
    cT
    wpo
    wemapsolem.1
    wph
    cA
    cvv
    wcel
    cA
    cR
    wor
    cB
    cS
    wpo
    #
    @1
    wemapsolem.2
    wemapsolem.3
    wph
    cB
    cS
    wor
    #
    @2
    wemapsolem.4
    cB
    cS
    sopo
    syl
    vx
    vy
    vz
    vw
    cA
    cB
    cR
    cS
    cT
    cvv
    wemapso.t
    wemappo
    syl3anc
    cU
    @0
    cT
    poss
    mpsyl
    wph
    va
    cv
    #
    cU
    wcel
    #
    vb
    cv
    #
    cU
    wcel
    #
    wa
    #
    wa
    #
    va
    vb
    weq
    #
    @6
    @4
    cT
    wbr
    #
    @4
    @6
    cT
    wbr
    #
    wo
    #
    wo
    #
    @12
    @10
    @11
    w3o
    #
    @9
    @10
    @13
    @10
    wn
    @4
    @6
    wne
    #
    @9
    @13
    @4
    @6
    df-ne
    wph
    @8
    @16
    @13
    wph
    @8
    @16
    wa
    #
    wa
    #
    vc
    cv
    #
    @6
    cfv
    #
    @19
    @4
    cfv
    #
    cS
    wbr
    #
    @21
    @20
    cS
    wbr
    #
    wo
    #
    vd
    cv
    #
    @19
    cR
    wbr
    #
    @25
    @6
    cfv
    #
    @25
    @4
    cfv
    #
    wceq
    #
    wi
    #
    vd
    cA
    wral
    #
    wa
    #
    vc
    cA
    wrex
    #
    @13
    @18
    @20
    @21
    wceq
    #
    wn
    #
    @31
    wa
    #
    vc
    cA
    wrex
    #
    @33
    @18
    @26
    wn
    #
    vd
    @4
    @6
    cdif
    cdm
    #
    wral
    #
    vc
    @39
    wrex
    @37
    wemapsolem.5
    @18
    @40
    @36
    vc
    @39
    cA
    @18
    @19
    @39
    wcel
    #
    @40
    wa
    @19
    cA
    wcel
    #
    @35
    wa
    #
    @31
    wa
    @42
    @36
    wa
    @18
    @41
    @43
    @40
    @31
    @18
    @41
    @19
    vx
    cv
    #
    @4
    cfv
    #
    @44
    @6
    cfv
    #
    wne
    #
    vx
    cA
    crab
    #
    wcel
    @43
    @18
    @39
    @48
    @19
    @18
    @4
    cA
    wfn
    #
    @6
    cA
    wfn
    #
    @39
    @48
    wceq
    @18
    cA
    cB
    @4
    wf
    #
    @49
    @18
    @4
    @0
    wcel
    @51
    @18
    cU
    @0
    @4
    wemapsolem.1
    wph
    @5
    @7
    @16
    simprll
    sseldi
    @4
    cB
    cA
    elmapi
    syl
    #
    cA
    cB
    @4
    ffn
    syl
    @18
    cA
    cB
    @6
    wf
    #
    @50
    @18
    @6
    @0
    wcel
    @53
    @18
    cU
    @0
    @6
    wemapsolem.1
    wph
    @5
    @7
    @16
    simprlr
    sseldi
    @6
    cB
    cA
    elmapi
    syl
    #
    cA
    cB
    @6
    ffn
    syl
    vx
    cA
    @4
    @6
    fndmdif
    syl2anc
    #
    eleq2d
    @47
    @35
    vx
    @19
    cA
    @47
    @46
    @45
    wceq
    #
    wn
    #
    vx
    vc
    weq
    #
    @35
    @45
    @46
    nesym
    #
    @58
    @56
    @34
    @58
    @46
    @20
    @45
    @21
    @44
    @19
    @6
    fveq2
    @44
    @19
    @4
    fveq2
    eqeq12d
    notbid
    syl5bb
    elrab
    syl6bb
    @18
    @38
    @30
    vd
    @39
    cA
    @18
    @25
    @39
    wcel
    #
    @38
    wi
    @25
    cA
    wcel
    #
    @29
    wn
    #
    wa
    #
    @38
    wi
    #
    @61
    @30
    wi
    #
    @18
    @60
    @63
    @38
    @18
    @60
    @25
    @48
    wcel
    @63
    @18
    @39
    @48
    @25
    @55
    eleq2d
    @47
    @62
    vx
    @25
    cA
    @47
    @57
    vx
    vd
    weq
    #
    @62
    @59
    @66
    @56
    @29
    @66
    @46
    @27
    @45
    @28
    @44
    @25
    @6
    fveq2
    @44
    @25
    @4
    fveq2
    eqeq12d
    notbid
    syl5bb
    elrab
    syl6bb
    imbi1d
    @64
    @61
    @62
    @38
    wi
    #
    wi
    @65
    @61
    @62
    @38
    impexp
    @30
    @67
    @61
    @26
    @29
    con34b
    imbi2i
    bitr4i
    syl6bb
    ralbidv2
    anbi12d
    @42
    @35
    @31
    anass
    syl6bb
    rexbidv2
    mpbid
    @18
    @36
    @32
    vc
    cA
    @18
    @42
    wa
    #
    @35
    @24
    @31
    @68
    @3
    @20
    cB
    wcel
    #
    @21
    cB
    wcel
    #
    @35
    @24
    wi
    wph
    @3
    @17
    @42
    wemapsolem.4
    ad2antrr
    @18
    cA
    cB
    @19
    @6
    @54
    ffvelrnda
    @18
    cA
    cB
    @19
    @4
    @52
    ffvelrnda
    @3
    @69
    @70
    wa
    wa
    #
    @24
    @35
    @71
    @34
    @24
    cB
    @20
    @21
    cS
    sotrieq
    con2bid
    biimprd
    syl12anc
    anim1d
    reximdva
    mpd
    @13
    @22
    @31
    wa
    #
    vc
    cA
    wrex
    #
    @23
    @26
    @28
    @27
    wceq
    #
    wi
    #
    vd
    cA
    wral
    #
    wa
    #
    vc
    cA
    wrex
    #
    wo
    @72
    @77
    wo
    #
    vc
    cA
    wrex
    @33
    @11
    @73
    @12
    @78
    @6
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    @11
    @73
    wb
    vb
    vex
    #
    va
    vex
    #
    vx
    vy
    vz
    vw
    cA
    @6
    @4
    cR
    cS
    cT
    cvv
    cvv
    vc
    vd
    wemapso.t
    wemaplem1
    mp2an
    @81
    @80
    @12
    @78
    wb
    @83
    @82
    vx
    vy
    vz
    vw
    cA
    @4
    @6
    cR
    cS
    cT
    cvv
    cvv
    vc
    vd
    wemapso.t
    wemaplem1
    mp2an
    orbi12i
    @72
    @77
    vc
    cA
    r19.43
    @79
    @32
    vc
    cA
    @32
    @72
    @23
    @31
    wa
    #
    wo
    @79
    @22
    @23
    @31
    andir
    @84
    @77
    @72
    @31
    @76
    @23
    @30
    @75
    vd
    cA
    @29
    @74
    @26
    @27
    @28
    eqcom
    imbi2i
    ralbii
    anbi2i
    orbi2i
    bitr2i
    rexbii
    3bitr2i
    sylibr
    expr
    syl5bir
    orrd
    @15
    @10
    @11
    @12
    w3o
    @14
    @12
    @10
    @11
    3orrot
    @10
    @11
    @12
    3orass
    bitr2i
    sylib
    issod
end
