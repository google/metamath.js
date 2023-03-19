include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cif.mm"
include "wcel.mm"
include "ifcld.mm"
include "weq.mm"
include "adantr.mm"
include "breq1.mm"
include "fveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "imp.mm"
include "breqtrd.mm"
include "wb.mm"
include "iftrue.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "adantl.mm"
include "mpbird.mm"
include "wpo.mm"
include "w3a.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "elmapi.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "3jca.mm"
include "syl5ibcom.mm"
include "potr.mm"
include "syl22anc.mm"
include "ifeq1.mm"
include "ifid.mm"
include "syl6eq.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "wor.mm"
include "sopo.mm"
include "po2nr.mm"
include "syl12anc.mm"
include "nan.mm"
include "mpbi.mm"
include "iffalse.mm"
include "w3o.mm"
include "solin.mm"
include "mpjao3dan.mm"
include "r19.26.mm"
include "sylanbrc.mm"
include "prth.mm"
include "eqtr.mm"
include "syl6.mm"
include "ralimi.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "soltmin.mm"
include "syl13anc.mm"
include "biimpd.mm"
include "imim1d.mm"
include "ralimdva.mm"
include "syl2im.mm"
include "mpd.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "wemaplem1.mm"

theorem wemaplem2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cU: class U
  let cZ: class Z
  assume wemapso.t: |- T = { <. x , y >. | E. z e. A ( ( x ` z ) S ( y ` z ) /\ A. w e. A ( w R z -> ( x ` w ) = ( y ` w ) ) ) }
  assume wemaplem2.a: |- ( ph -> A e. _V )
  assume wemaplem2.p: |- ( ph -> P e. ( B ^m A ) )
  assume wemaplem2.x: |- ( ph -> X e. ( B ^m A ) )
  assume wemaplem2.q: |- ( ph -> Q e. ( B ^m A ) )
  assume wemaplem2.r: |- ( ph -> R Or A )
  assume wemaplem2.s: |- ( ph -> S Po B )
  assume wemaplem2.px1: |- ( ph -> a e. A )
  assume wemaplem2.px2: |- ( ph -> ( P ` a ) S ( X ` a ) )
  assume wemaplem2.px3: |- ( ph -> A. c e. A ( c R a -> ( P ` c ) = ( X ` c ) ) )
  assume wemaplem2.xq1: |- ( ph -> b e. A )
  assume wemaplem2.xq2: |- ( ph -> ( X ` b ) S ( Q ` b ) )
  assume wemaplem2.xq3: |- ( ph -> A. c e. A ( c R b -> ( X ` c ) = ( Q ` c ) ) )

  disjoint a b
  disjoint a c
  disjoint a x
  disjoint B a
  disjoint b c
  disjoint b x
  disjoint B b
  disjoint c x
  disjoint B c
  disjoint B x
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint a w
  disjoint a y
  disjoint a z
  disjoint X a
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint X b
  disjoint c w
  disjoint c y
  disjoint c z
  disjoint X c
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint X w
  disjoint x y
  disjoint x z
  disjoint X x
  disjoint y z
  disjoint X y
  disjoint X z
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q w
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint d ph
  disjoint a d
  disjoint b d
  disjoint c d
  disjoint d x
  disjoint B d
  disjoint T d
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U d
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint P d
  disjoint Q d
  disjoint R d
  disjoint S d
  disjoint Z c
  disjoint Z d
  disjoint Z x
  assert |- ( ph -> P T Q )

  proof
    wph
    cP
    cQ
    cT
    wbr
    #
    vd
    cv
    #
    cP
    cfv
    #
    @1
    cQ
    cfv
    #
    cS
    wbr
    #
    vc
    cv
    #
    @1
    cR
    wbr
    #
    @5
    cP
    cfv
    #
    @5
    cQ
    cfv
    #
    wceq
    #
    wi
    #
    vc
    cA
    wral
    #
    wa
    #
    vd
    cA
    wrex
    #
    wph
    va
    cv
    #
    vb
    cv
    #
    cR
    wbr
    #
    @14
    @15
    cif
    #
    cA
    wcel
    @17
    cP
    cfv
    #
    @17
    cQ
    cfv
    #
    cS
    wbr
    #
    @5
    @17
    cR
    wbr
    #
    @9
    wi
    #
    vc
    cA
    wral
    #
    @13
    wph
    @16
    @14
    @15
    cA
    wemaplem2.px1
    wemaplem2.xq1
    ifcld
    wph
    @16
    @20
    va
    vb
    weq
    #
    @15
    @14
    cR
    wbr
    #
    wph
    @16
    wa
    #
    @20
    @14
    cP
    cfv
    #
    @14
    cQ
    cfv
    #
    cS
    wbr
    #
    @26
    @27
    @14
    cX
    cfv
    #
    @28
    cS
    wph
    @27
    @30
    cS
    wbr
    #
    @16
    wemaplem2.px2
    adantr
    wph
    @16
    @30
    @28
    wceq
    #
    wph
    @14
    cA
    wcel
    #
    @5
    @15
    cR
    wbr
    #
    @5
    cX
    cfv
    #
    @8
    wceq
    #
    wi
    #
    vc
    cA
    wral
    #
    @16
    @32
    wi
    #
    wemaplem2.px1
    wemaplem2.xq3
    @37
    @39
    vc
    @14
    cA
    vc
    va
    weq
    #
    @34
    @16
    @36
    @32
    @5
    @14
    @15
    cR
    breq1
    @40
    @35
    @30
    @8
    @28
    @5
    @14
    cX
    fveq2
    @5
    @14
    cQ
    fveq2
    eqeq12d
    imbi12d
    rspcva
    syl2anc
    imp
    breqtrd
    @16
    @20
    @29
    wb
    wph
    @16
    @18
    @27
    @19
    @28
    cS
    @16
    @17
    @14
    cP
    @16
    @14
    @15
    iftrue
    #
    fveq2d
    @16
    @17
    @14
    cQ
    @41
    fveq2d
    breq12d
    adantl
    mpbird
    wph
    @24
    wa
    #
    @20
    @15
    cP
    cfv
    #
    @15
    cQ
    cfv
    #
    cS
    wbr
    #
    @42
    cB
    cS
    wpo
    #
    @43
    cB
    wcel
    #
    @15
    cX
    cfv
    #
    cB
    wcel
    #
    @44
    cB
    wcel
    #
    w3a
    #
    @43
    @48
    cS
    wbr
    #
    @48
    @44
    cS
    wbr
    #
    @45
    wph
    @46
    @24
    wemaplem2.s
    adantr
    wph
    @51
    @24
    wph
    @47
    @49
    @50
    wph
    cA
    cB
    @15
    cP
    wph
    cP
    cB
    cA
    cmap
    co
    #
    wcel
    #
    cA
    cB
    cP
    wf
    wemaplem2.p
    cP
    cB
    cA
    elmapi
    syl
    wemaplem2.xq1
    ffvelrnd
    wph
    cA
    cB
    @15
    cX
    wph
    cX
    @54
    wcel
    cA
    cB
    cX
    wf
    wemaplem2.x
    cX
    cB
    cA
    elmapi
    syl
    wemaplem2.xq1
    ffvelrnd
    wph
    cA
    cB
    @15
    cQ
    wph
    cQ
    @54
    wcel
    #
    cA
    cB
    cQ
    wf
    wemaplem2.q
    cQ
    cB
    cA
    elmapi
    syl
    wemaplem2.xq1
    ffvelrnd
    3jca
    adantr
    wph
    @24
    @52
    wph
    @31
    @24
    @52
    wemaplem2.px2
    @24
    @27
    @43
    @30
    @48
    cS
    @14
    @15
    cP
    fveq2
    @14
    @15
    cX
    fveq2
    breq12d
    syl5ibcom
    imp
    wph
    @53
    @24
    wemaplem2.xq2
    adantr
    @46
    @51
    wa
    @52
    @53
    wa
    @45
    cB
    @43
    @48
    @44
    cS
    potr
    imp
    syl22anc
    @24
    @20
    @45
    wb
    #
    wph
    @24
    @18
    @43
    @19
    @44
    cS
    @24
    @17
    @15
    cP
    @24
    @17
    @16
    @15
    @15
    cif
    @15
    @16
    @14
    @15
    @15
    ifeq1
    @16
    @15
    ifid
    syl6eq
    #
    fveq2d
    @24
    @17
    @15
    cQ
    @58
    fveq2d
    breq12d
    adantl
    mpbird
    wph
    @25
    wa
    #
    @20
    @45
    @59
    @43
    @48
    @44
    cS
    wph
    @25
    @43
    @48
    wceq
    #
    wph
    @15
    cA
    wcel
    #
    @5
    @14
    cR
    wbr
    #
    @7
    @35
    wceq
    #
    wi
    #
    vc
    cA
    wral
    #
    @25
    @60
    wi
    #
    wemaplem2.xq1
    wemaplem2.px3
    @64
    @66
    vc
    @15
    cA
    vc
    vb
    weq
    #
    @62
    @25
    @63
    @60
    @5
    @15
    @14
    cR
    breq1
    @67
    @7
    @43
    @35
    @48
    @5
    @15
    cP
    fveq2
    @5
    @15
    cX
    fveq2
    eqeq12d
    imbi12d
    rspcva
    syl2anc
    imp
    wph
    @53
    @25
    wemaplem2.xq2
    adantr
    eqbrtrd
    @59
    @16
    wn
    #
    @57
    wph
    @25
    @16
    wa
    wn
    #
    wi
    @59
    @68
    wi
    wph
    cA
    cR
    wpo
    #
    @61
    @33
    @69
    wph
    cA
    cR
    wor
    #
    @70
    wemaplem2.r
    cA
    cR
    sopo
    syl
    wemaplem2.xq1
    wemaplem2.px1
    cA
    @15
    @14
    cR
    po2nr
    syl12anc
    wph
    @25
    @16
    nan
    mpbi
    @68
    @18
    @43
    @19
    @44
    cS
    @68
    @17
    @15
    cP
    @16
    @14
    @15
    iffalse
    #
    fveq2d
    @68
    @17
    @15
    cQ
    @72
    fveq2d
    breq12d
    syl
    mpbird
    wph
    @71
    @33
    @61
    @16
    @24
    @25
    w3o
    wemaplem2.r
    wemaplem2.px1
    wemaplem2.xq1
    cA
    @14
    @15
    cR
    solin
    syl12anc
    mpjao3dan
    wph
    @64
    @37
    wa
    #
    vc
    cA
    wral
    #
    @23
    wph
    @65
    @38
    @74
    wemaplem2.px3
    wemaplem2.xq3
    @64
    @37
    vc
    cA
    r19.26
    sylanbrc
    wph
    @71
    @33
    @61
    w3a
    #
    @74
    @62
    @34
    wa
    #
    @9
    wi
    #
    vc
    cA
    wral
    @23
    wph
    @71
    @33
    @61
    wemaplem2.r
    wemaplem2.px1
    wemaplem2.xq1
    3jca
    @73
    @77
    vc
    cA
    @73
    @76
    @63
    @36
    wa
    @9
    @62
    @63
    @34
    @36
    prth
    @7
    @35
    @8
    eqtr
    syl6
    ralimi
    @75
    @77
    @22
    vc
    cA
    @75
    @5
    cA
    wcel
    #
    wa
    #
    @21
    @76
    @9
    @79
    @21
    @76
    @79
    @71
    @78
    @33
    @61
    @21
    @76
    wb
    @71
    @33
    @61
    @78
    simpl1
    @75
    @78
    simpr
    @71
    @33
    @61
    @78
    simpl2
    @71
    @33
    @61
    @78
    simpl3
    @5
    @14
    @15
    cR
    cA
    soltmin
    syl13anc
    biimpd
    imim1d
    ralimdva
    syl2im
    mpd
    @12
    @20
    @23
    wa
    vd
    @17
    cA
    @1
    @17
    wceq
    #
    @4
    @20
    @11
    @23
    @80
    @2
    @18
    @3
    @19
    cS
    @1
    @17
    cP
    fveq2
    @1
    @17
    cQ
    fveq2
    breq12d
    @80
    @10
    @22
    vc
    cA
    @80
    @6
    @21
    @9
    @1
    @17
    @5
    cR
    breq2
    imbi1d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    wph
    @55
    @56
    @0
    @13
    wb
    wemaplem2.p
    wemaplem2.q
    vx
    vy
    vz
    vw
    cA
    cP
    cQ
    cR
    cS
    cT
    @54
    @54
    vd
    vc
    wemapso.t
    wemaplem1
    syl2anc
    mpbird
end
