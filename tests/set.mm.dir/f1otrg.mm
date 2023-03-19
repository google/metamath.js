include "cstrkgc.mm"
include "cstrkgb.mm"
include "cin.mm"
include "cstrkgcb.mm"
include "cv.mm"
include "clng.mm"
include "cfv.mm"
include "csn.mm"
include "cdif.mm"
include "co.mm"
include "wcel.mm"
include "w3o.mm"
include "crab.mm"
include "cmpt2.mm"
include "wceq.mm"
include "citv.mm"
include "wsbc.mm"
include "cbs.mm"
include "cab.mm"
include "cstrkg.mm"
include "cvv.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "elex.mm"
include "syl.mm"
include "adantr.mm"
include "wf.mm"
include "wf1o.mm"
include "f1of.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "simprr.mm"
include "axtgcgrrflx.mm"
include "adantlr.mm"
include "w3a.mm"
include "wb.mm"
include "f1otrgds.mm"
include "3eqtr4d.mm"
include "ralrimivva.mm"
include "wf1.mm"
include "f1of1.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "simp22.mm"
include "jca.mm"
include "simp23.mm"
include "simp3.mm"
include "3ad2antl1.mm"
include "3eqtr3d.mm"
include "axtgcgrid.mm"
include "f1veqaeq.mm"
include "imp.mm"
include "syl21anc.mm"
include "3expia.mm"
include "ralrimivvva.mm"
include "istrkgc.mm"
include "sylanbrc.mm"
include "wrex.mm"
include "cpw.mm"
include "simp2.mm"
include "3adant3.mm"
include "f1otrgitv.mm"
include "mpbid.mm"
include "axtgbtwnid.mm"
include "ccnv.mm"
include "f1ocnv.mm"
include "3syl.mm"
include "ad5antr.mm"
include "simplr.mm"
include "simpr.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "ad2antrr.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "simplll.mm"
include "sylancom.mm"
include "simplr2.mm"
include "simplr3.mm"
include "rspcedvd.mm"
include "simplr1.mm"
include "axtgpasch.mm"
include "r19.29a.mm"
include "ex.mm"
include "cima.mm"
include "simpllr.mm"
include "wfn.mm"
include "wss.mm"
include "ffn.mm"
include "simp-4r.mm"
include "simpld.mm"
include "elpwid.mm"
include "fnfvima.mm"
include "syl3anc.mm"
include "simprd.mm"
include "oveq1.mm"
include "eleq2d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "eqeltrd.mm"
include "ad4antr.mm"
include "simp-5l.mm"
include "sseldd.mm"
include "adantllr.mm"
include "eleq1.mm"
include "2ralbidv.mm"
include "adantl.mm"
include "rspcedv.mm"
include "mpd.mm"
include "ad3antrrr.mm"
include "crn.mm"
include "imassrn.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl5sseq.mm"
include "4syl.mm"
include "simp-5r.mm"
include "f1imacnv.mm"
include "eleqtrd.mm"
include "simp-6l.mm"
include "f1ocnvdm.mm"
include "oveq2d.mm"
include "3eltr3d.mm"
include "3impa.mm"
include "axtgcont.mm"
include "r19.29an.mm"
include "3jca.mm"
include "istrkgb.mm"
include "elind.mm"
include "wne.mm"
include "ad9antr.mm"
include "simp-9r.mm"
include "simp-8r.mm"
include "simp-7r.mm"
include "simp-6r.mm"
include "simprl1.mm"
include "dff1o6.mm"
include "simp3bi.mm"
include "r19.21bi.mm"
include "necon3d.mm"
include "simprl2.mm"
include "simprl3.mm"
include "axtg5seg.mm"
include "ralrimiva.mm"
include "simp-4l.mm"
include "eleqtrrd.mm"
include "sylan.mm"
include "ffvelrnda.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "eqeq1d.mm"
include "syl22anc.mm"
include "axtgsegcon.mm"
include "jca32.mm"
include "istrkgcb.mm"
include "sylibr.mm"
include "istrkgl.mm"
include "df-trkg.mm"
include "syl6eleqr.mm"

theorem f1otrg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cD: class D
  let cP: class P
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vp: setvar p
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume f1otrkg.p: |- P = ( Base ` G )
  assume f1otrkg.d: |- D = ( dist ` G )
  assume f1otrkg.i: |- I = ( Itv ` G )
  assume f1otrkg.b: |- B = ( Base ` H )
  assume f1otrkg.e: |- E = ( dist ` H )
  assume f1otrkg.j: |- J = ( Itv ` H )
  assume f1otrkg.f: |- ( ph -> F : B -1-1-onto-> P )
  assume f1otrkg.1: |- ( ( ph /\ ( e e. B /\ f e. B ) ) -> ( e E f ) = ( ( F ` e ) D ( F ` f ) ) )
  assume f1otrkg.2: |- ( ( ph /\ ( e e. B /\ f e. B /\ g e. B ) ) -> ( g e. ( e J f ) <-> ( F ` g ) e. ( ( F ` e ) I ( F ` f ) ) ) )
  assume f1otrg.h: |- ( ph -> H e. V )
  assume f1otrg.g: |- ( ph -> G e. TarskiG )
  assume f1otrg.l: |- ( ph -> ( LineG ` H ) = ( x e. B , y e. ( B \ { x } ) |-> { z e. B | ( z e. ( x J y ) \/ x e. ( z J y ) \/ y e. ( x J z ) ) } ) )

  disjoint e f
  disjoint e g
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint B e
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint D e
  disjoint D f
  disjoint D g
  disjoint E e
  disjoint E f
  disjoint E g
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint I e
  disjoint I f
  disjoint I g
  disjoint I x
  disjoint I y
  disjoint J e
  disjoint J f
  disjoint J g
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint P e
  disjoint P f
  disjoint P g
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint e ph
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint H f
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint a i
  disjoint a p
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint B a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b i
  disjoint b p
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c i
  disjoint c p
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d i
  disjoint d p
  disjoint d s
  disjoint d t
  disjoint d u
  disjoint d v
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint B d
  disjoint e i
  disjoint e p
  disjoint e s
  disjoint e t
  disjoint e u
  disjoint e v
  disjoint e w
  disjoint f i
  disjoint f p
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g i
  disjoint g p
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint i p
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint B i
  disjoint p s
  disjoint p t
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint B p
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint D c
  disjoint D d
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint E i
  disjoint E p
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint I a
  disjoint I c
  disjoint I d
  disjoint I u
  disjoint I v
  disjoint I w
  disjoint J a
  disjoint J b
  disjoint J c
  disjoint J d
  disjoint J i
  disjoint J p
  disjoint J s
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint H i
  disjoint H p
  assert |- ( ph -> H e. TarskiG )

  proof
    wph
    cH
    cstrkgc
    cstrkgb
    cin
    #
    cstrkgcb
    vf
    cv
    #
    clng
    cfv
    vx
    vy
    vp
    cv
    #
    @2
    vx
    cv
    #
    csn
    #
    cdif
    vz
    cv
    #
    @3
    vy
    cv
    #
    vi
    cv
    #
    co
    wcel
    @3
    @5
    @6
    @7
    co
    wcel
    @6
    @3
    @5
    @7
    co
    wcel
    w3o
    vz
    @2
    crab
    cmpt2
    wceq
    vi
    @1
    citv
    cfv
    wsbc
    vp
    @1
    cbs
    cfv
    wsbc
    vf
    cab
    #
    cin
    #
    cin
    cstrkg
    wph
    @0
    @9
    cH
    wph
    cstrkgc
    cstrkgb
    cH
    wph
    cH
    cvv
    wcel
    #
    @3
    @6
    cE
    co
    #
    @6
    @3
    cE
    co
    #
    wceq
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @11
    @5
    @5
    cE
    co
    #
    wceq
    #
    @3
    @6
    wceq
    #
    wi
    #
    vz
    cB
    wral
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    cH
    cstrkgc
    wcel
    wph
    cH
    cV
    wcel
    @10
    f1otrg.h
    cH
    cV
    elex
    syl
    #
    wph
    @14
    @19
    wph
    @13
    vx
    vy
    cB
    cB
    wph
    @3
    cB
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    wa
    #
    @3
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    cD
    co
    #
    @26
    @25
    cD
    co
    @11
    @12
    @24
    cP
    cG
    cI
    cD
    @25
    @26
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    wph
    cG
    cstrkg
    wcel
    #
    @23
    f1otrg.g
    adantr
    #
    @24
    cB
    cP
    @3
    cF
    wph
    cB
    cP
    cF
    wf
    #
    @23
    wph
    cB
    cP
    cF
    wf1o
    #
    @30
    f1otrkg.f
    cB
    cP
    cF
    f1of
    #
    syl
    #
    adantr
    #
    wph
    @21
    @22
    simprl
    #
    ffvelrnd
    #
    @24
    cB
    cP
    @6
    cF
    @34
    wph
    @21
    @22
    simprr
    #
    ffvelrnd
    #
    axtgcgrrflx
    @24
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @3
    @6
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    wph
    @31
    @23
    f1otrkg.f
    adantr
    #
    wph
    ve
    cv
    #
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    wa
    #
    @40
    @1
    cE
    co
    @40
    cF
    cfv
    #
    @1
    cF
    cfv
    #
    cD
    co
    wceq
    #
    @23
    f1otrkg.1
    adantlr
    #
    wph
    @41
    @42
    vg
    cv
    #
    cB
    wcel
    w3a
    #
    @48
    @40
    @1
    cJ
    co
    wcel
    @48
    cF
    cfv
    @44
    @45
    cI
    co
    wcel
    wb
    #
    @23
    f1otrkg.2
    adantlr
    #
    @35
    @37
    f1otrgds
    @24
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @6
    @3
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @39
    @47
    @51
    @37
    @35
    f1otrgds
    3eqtr4d
    ralrimivva
    wph
    @18
    vx
    vy
    vz
    cB
    cB
    cB
    wph
    @21
    @22
    @5
    cB
    wcel
    #
    w3a
    #
    @16
    @17
    wph
    @53
    @16
    w3a
    #
    cB
    cP
    cF
    wf1
    #
    @23
    @25
    @26
    wceq
    #
    @17
    wph
    @53
    @55
    @16
    wph
    @31
    @55
    f1otrkg.f
    cB
    cP
    cF
    f1of1
    #
    syl
    3ad2ant1
    @54
    @21
    @22
    wph
    @21
    @22
    @52
    @16
    simp21
    #
    wph
    @21
    @22
    @52
    @16
    simp22
    #
    jca
    @54
    cP
    cG
    cI
    cD
    @25
    @26
    @5
    cF
    cfv
    #
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    wph
    @53
    @28
    @16
    f1otrg.g
    3ad2ant1
    @54
    cB
    cP
    @3
    cF
    wph
    @53
    @30
    @16
    @33
    3ad2ant1
    #
    @58
    ffvelrnd
    @54
    cB
    cP
    @6
    cF
    @61
    @59
    ffvelrnd
    @54
    cB
    cP
    @5
    cF
    @61
    wph
    @21
    @22
    @52
    @16
    simp23
    #
    ffvelrnd
    @54
    @11
    @15
    @27
    @60
    @60
    cD
    co
    wph
    @53
    @16
    simp3
    @54
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @3
    @6
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    wph
    @53
    @31
    @16
    f1otrkg.f
    3ad2ant1
    #
    wph
    @53
    @43
    @46
    @16
    f1otrkg.1
    3ad2antl1
    #
    wph
    @53
    @49
    @50
    @16
    f1otrkg.2
    3ad2antl1
    #
    @58
    @59
    f1otrgds
    @54
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @5
    @5
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @63
    @64
    @65
    @62
    @62
    f1otrgds
    3eqtr3d
    axtgcgrid
    @55
    @23
    wa
    @56
    @17
    cB
    cP
    @3
    @6
    cF
    f1veqaeq
    imp
    #
    syl21anc
    3expia
    ralrimivvva
    jca
    vx
    vy
    vz
    cB
    cH
    cJ
    cE
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    istrkgc
    sylanbrc
    wph
    @10
    @6
    @3
    @3
    cJ
    co
    wcel
    #
    @17
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    vu
    cv
    #
    @3
    @5
    cJ
    co
    #
    wcel
    #
    vv
    cv
    #
    @6
    @5
    cJ
    co
    wcel
    #
    wa
    #
    va
    cv
    #
    @70
    @6
    cJ
    co
    #
    wcel
    #
    @76
    @73
    @3
    cJ
    co
    #
    wcel
    #
    wa
    #
    va
    cB
    wrex
    #
    wi
    #
    vv
    cB
    wral
    vu
    cB
    wral
    vz
    cB
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @3
    @76
    @6
    cJ
    co
    #
    wcel
    #
    vy
    vt
    cv
    #
    wral
    vx
    vs
    cv
    #
    wral
    #
    va
    cB
    wrex
    #
    vb
    cv
    #
    @3
    @6
    cJ
    co
    #
    wcel
    #
    vy
    @88
    wral
    vx
    @89
    wral
    #
    vb
    cB
    wrex
    #
    wi
    #
    vt
    cB
    cpw
    #
    wral
    vs
    @98
    wral
    #
    w3a
    cH
    cstrkgb
    wcel
    @20
    wph
    @69
    @85
    @99
    wph
    @68
    vx
    vy
    cB
    cB
    wph
    @23
    @67
    @17
    wph
    @23
    @67
    w3a
    #
    @55
    @23
    @56
    @17
    @100
    @31
    @55
    wph
    @23
    @31
    @67
    f1otrkg.f
    3ad2ant1
    #
    @57
    syl
    wph
    @23
    @67
    simp2
    @100
    cP
    cG
    cI
    cD
    @25
    @26
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    wph
    @23
    @28
    @67
    f1otrg.g
    3ad2ant1
    wph
    @23
    @25
    cP
    wcel
    #
    @67
    @36
    3adant3
    wph
    @23
    @26
    cP
    wcel
    #
    @67
    @38
    3adant3
    @100
    @67
    @26
    @25
    @25
    cI
    co
    wcel
    wph
    @23
    @67
    simp3
    @100
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @3
    @3
    @6
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @101
    wph
    @23
    @43
    @46
    @67
    f1otrkg.1
    3ad2antl1
    wph
    @23
    @49
    @50
    @67
    f1otrkg.2
    3ad2antl1
    wph
    @23
    @21
    @67
    @35
    3adant3
    #
    @104
    wph
    @23
    @22
    @67
    @37
    3adant3
    f1otrgitv
    mpbid
    axtgbtwnid
    @66
    syl21anc
    3expia
    ralrimivva
    wph
    @84
    vx
    vy
    cB
    cB
    @24
    @83
    vz
    vu
    vv
    cB
    cB
    cB
    @24
    @52
    @70
    cB
    wcel
    #
    @73
    cB
    wcel
    #
    w3a
    #
    wa
    #
    @75
    @82
    @108
    @75
    wa
    #
    vc
    cv
    #
    @70
    cF
    cfv
    #
    @26
    cI
    co
    #
    wcel
    #
    @110
    @73
    cF
    cfv
    #
    @25
    cI
    co
    #
    wcel
    #
    wa
    #
    @82
    vc
    cP
    @109
    @110
    cP
    wcel
    #
    wa
    #
    @117
    wa
    #
    @81
    @110
    cF
    ccnv
    #
    cfv
    #
    @77
    wcel
    #
    @122
    @79
    wcel
    #
    wa
    va
    @122
    cB
    @120
    cP
    cB
    @110
    @121
    wph
    cP
    cB
    @121
    wf
    #
    @23
    @107
    @75
    @118
    @117
    wph
    @31
    cP
    cB
    @121
    wf1o
    #
    @125
    f1otrkg.f
    cB
    cP
    cF
    f1ocnv
    #
    cP
    cB
    @121
    f1of
    #
    3syl
    #
    ad5antr
    @109
    @118
    @117
    simplr
    #
    ffvelrnd
    #
    @120
    @76
    @122
    wceq
    #
    wa
    #
    @78
    @123
    @80
    @124
    @133
    @76
    @122
    @77
    @120
    @132
    simpr
    #
    eleq1d
    @133
    @76
    @122
    @79
    @134
    eleq1d
    anbi12d
    @120
    @123
    @124
    @120
    @123
    @122
    cF
    cfv
    #
    @112
    wcel
    #
    @120
    @136
    @113
    @119
    @113
    @116
    simprl
    @120
    @31
    @118
    @136
    @113
    wb
    @109
    @31
    @118
    @117
    @24
    @31
    @107
    @75
    @39
    ad2antrr
    #
    ad2antrr
    #
    @130
    @31
    @118
    wa
    #
    @135
    @110
    @112
    cB
    cP
    @110
    cF
    f1ocnvfv2
    #
    eleq1d
    syl2anc
    mpbird
    @120
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @70
    @6
    @122
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @138
    @120
    @43
    @109
    @46
    @109
    @118
    @117
    @43
    simplll
    @109
    @43
    @24
    @46
    @24
    @107
    @75
    @43
    simplll
    @47
    sylancom
    #
    sylancom
    #
    @120
    @49
    @109
    @50
    @109
    @118
    @117
    @49
    simplll
    @109
    @49
    @24
    @50
    @24
    @107
    @75
    @49
    simplll
    @51
    sylancom
    #
    sylancom
    #
    @109
    @105
    @118
    @117
    @52
    @105
    @106
    @24
    @75
    simplr2
    #
    ad2antrr
    @109
    @22
    @118
    @117
    @24
    @22
    @107
    @75
    @37
    ad2antrr
    #
    ad2antrr
    @131
    f1otrgitv
    mpbird
    @120
    @124
    @135
    @115
    wcel
    #
    @120
    @147
    @116
    @119
    @113
    @116
    simprr
    @120
    @31
    @118
    @147
    @116
    wb
    @138
    @130
    @139
    @135
    @110
    @115
    @140
    eleq1d
    syl2anc
    mpbird
    @120
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @73
    @3
    @122
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @138
    @142
    @144
    @109
    @106
    @118
    @117
    @52
    @105
    @106
    @24
    @75
    simplr3
    #
    ad2antrr
    @109
    @21
    @118
    @117
    @24
    @21
    @107
    @75
    @35
    ad2antrr
    #
    ad2antrr
    @131
    f1otrgitv
    mpbird
    jca
    rspcedvd
    @109
    cP
    @111
    cG
    cI
    cD
    @114
    @25
    @26
    @60
    vc
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    @24
    @28
    @107
    @75
    @29
    ad2antrr
    @109
    cB
    cP
    @3
    cF
    @24
    @30
    @107
    @75
    @34
    ad2antrr
    #
    @149
    ffvelrnd
    @109
    cB
    cP
    @6
    cF
    @150
    @146
    ffvelrnd
    @109
    cB
    cP
    @5
    cF
    @150
    @52
    @105
    @106
    @24
    @75
    simplr1
    #
    ffvelrnd
    @109
    cB
    cP
    @70
    cF
    @150
    @145
    ffvelrnd
    @109
    cB
    cP
    @73
    cF
    @150
    @148
    ffvelrnd
    @109
    @72
    @111
    @25
    @60
    cI
    co
    #
    wcel
    @108
    @72
    @74
    simprl
    @109
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @3
    @5
    @70
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @137
    @141
    @143
    @149
    @151
    @145
    f1otrgitv
    mpbid
    @109
    @74
    @114
    @26
    @60
    cI
    co
    wcel
    @108
    @72
    @74
    simprr
    @109
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @6
    @5
    @73
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @137
    @141
    @143
    @146
    @151
    @148
    f1otrgitv
    mpbid
    axtgpasch
    r19.29a
    ex
    ralrimivvva
    ralrimivva
    wph
    @97
    vs
    vt
    @98
    @98
    wph
    @89
    @98
    wcel
    #
    @88
    @98
    wcel
    #
    wa
    #
    wa
    #
    @91
    @96
    @156
    @90
    @96
    va
    cB
    @156
    @76
    cB
    wcel
    #
    wa
    #
    @90
    wa
    #
    @110
    @40
    @1
    cI
    co
    #
    wcel
    #
    vf
    cF
    @88
    cima
    #
    wral
    ve
    cF
    @89
    cima
    #
    wral
    #
    @96
    vc
    cP
    @159
    @118
    wa
    #
    @164
    wa
    @122
    @93
    wcel
    #
    vy
    @88
    wral
    vx
    @89
    wral
    #
    @96
    @158
    @118
    @164
    @167
    @90
    @158
    @118
    wa
    #
    @164
    wa
    #
    @166
    vx
    vy
    @89
    @88
    @169
    @3
    @89
    wcel
    #
    @6
    @88
    wcel
    #
    wa
    #
    wa
    #
    @166
    @135
    @25
    @26
    cI
    co
    #
    wcel
    #
    @173
    @135
    @110
    @174
    @173
    @31
    @118
    @135
    @110
    wceq
    wph
    @31
    @155
    @157
    @118
    @164
    @172
    f1otrkg.f
    ad5antr
    #
    @158
    @118
    @164
    @172
    simpllr
    @140
    syl2anc
    @173
    @25
    @163
    wcel
    #
    @26
    @162
    wcel
    #
    @164
    @110
    @174
    wcel
    #
    @173
    cF
    cB
    wfn
    #
    @89
    cB
    wss
    #
    @170
    @177
    @173
    @31
    @30
    @180
    @176
    @32
    cB
    cP
    cF
    ffn
    3syl
    #
    @168
    @172
    @181
    @164
    @168
    @172
    wa
    #
    @89
    cB
    @183
    @153
    @154
    wph
    @155
    @157
    @118
    @172
    simp-4r
    #
    simpld
    elpwid
    #
    adantlr
    @169
    @170
    @171
    simprl
    cB
    @89
    cF
    @3
    fnfvima
    syl3anc
    @173
    @180
    @88
    cB
    wss
    #
    @171
    @178
    @182
    @168
    @172
    @186
    @164
    @183
    @88
    cB
    @183
    @153
    @154
    @184
    simprd
    elpwid
    #
    adantlr
    @169
    @170
    @171
    simprr
    cB
    @88
    cF
    @6
    fnfvima
    syl3anc
    @168
    @164
    @172
    simplr
    @161
    @179
    @110
    @25
    @1
    cI
    co
    #
    wcel
    ve
    vf
    @25
    @26
    @163
    @162
    @40
    @25
    wceq
    @160
    @188
    @110
    @40
    @25
    @1
    cI
    oveq1
    eleq2d
    @1
    @26
    wceq
    @188
    @174
    @110
    @1
    @26
    @25
    cI
    oveq2
    eleq2d
    rspc2va
    syl21anc
    eqeltrd
    @168
    @172
    @166
    @175
    wb
    @164
    @183
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @3
    @6
    @122
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    wph
    @31
    @155
    @157
    @118
    @172
    f1otrkg.f
    ad4antr
    @183
    @43
    wph
    @46
    wph
    @155
    @157
    @118
    @172
    @43
    simp-5l
    f1otrkg.1
    sylancom
    @183
    @49
    wph
    @50
    wph
    @155
    @157
    @118
    @172
    @49
    simp-5l
    f1otrkg.2
    sylancom
    @183
    @89
    cB
    @3
    @185
    @168
    @170
    @171
    simprl
    sseldd
    @183
    @88
    cB
    @6
    @187
    @168
    @170
    @171
    simprr
    sseldd
    @183
    cP
    cB
    @110
    @121
    wph
    @125
    @155
    @157
    @118
    @172
    @129
    ad4antr
    @158
    @118
    @172
    simplr
    ffvelrnd
    f1otrgitv
    adantlr
    mpbird
    ralrimivva
    adantllr
    @165
    @167
    @96
    wi
    @164
    @165
    @95
    @167
    vb
    @122
    cB
    @165
    cP
    cB
    @110
    @121
    wph
    @125
    @155
    @157
    @90
    @118
    @129
    ad4antr
    @159
    @118
    simpr
    ffvelrnd
    @92
    @122
    wceq
    #
    @95
    @167
    wb
    @165
    @189
    @94
    @166
    vx
    vy
    @89
    @88
    @92
    @122
    @93
    eleq1
    2ralbidv
    adantl
    rspcedv
    adantr
    mpd
    @159
    ve
    vf
    vv
    vu
    @76
    cF
    cfv
    #
    cP
    @163
    @162
    cG
    cI
    cD
    vc
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    wph
    @28
    @155
    @157
    @90
    f1otrg.g
    ad3antrrr
    @159
    cF
    crn
    #
    @163
    cP
    cF
    @89
    imassrn
    wph
    @191
    cP
    wceq
    #
    @155
    @157
    @90
    wph
    @31
    cB
    cP
    cF
    wfo
    @192
    f1otrkg.f
    cB
    cP
    cF
    f1ofo
    cB
    cP
    cF
    forn
    3syl
    ad3antrrr
    #
    syl5sseq
    #
    @159
    @191
    @162
    cP
    cF
    @88
    imassrn
    @193
    syl5sseq
    #
    @159
    cB
    cP
    @76
    cF
    wph
    @30
    @155
    @157
    @90
    @33
    ad3antrrr
    @156
    @157
    @90
    simplr
    ffvelrnd
    @159
    @70
    @163
    wcel
    #
    @73
    @162
    wcel
    #
    @70
    @190
    @73
    cI
    co
    #
    wcel
    @159
    @196
    wa
    #
    @197
    wa
    #
    @70
    @121
    cfv
    #
    cF
    cfv
    #
    @190
    @73
    @121
    cfv
    #
    cF
    cfv
    #
    cI
    co
    #
    @70
    @198
    @200
    @201
    @76
    @203
    cJ
    co
    #
    wcel
    #
    @202
    @205
    wcel
    @200
    @201
    @89
    wcel
    @203
    @88
    wcel
    @90
    @207
    @200
    @201
    @121
    @163
    cima
    #
    @89
    @200
    @121
    cP
    wfn
    #
    @163
    cP
    wss
    #
    @196
    @201
    @208
    wcel
    @200
    @31
    @126
    @125
    @209
    wph
    @31
    @155
    @157
    @90
    @196
    @197
    f1otrkg.f
    ad5antr
    #
    @127
    @128
    cP
    cB
    @121
    ffn
    4syl
    #
    @159
    @210
    @196
    @197
    @194
    ad2antrr
    #
    @159
    @196
    @197
    simplr
    #
    cP
    @163
    @121
    @70
    fnfvima
    syl3anc
    @200
    @55
    @181
    @208
    @89
    wceq
    @200
    @31
    @55
    @211
    @57
    syl
    #
    @200
    @89
    cB
    @200
    @153
    @154
    wph
    @155
    @157
    @90
    @196
    @197
    simp-5r
    #
    simpld
    elpwid
    cB
    cP
    @89
    cF
    f1imacnv
    syl2anc
    eleqtrd
    @200
    @203
    @121
    @162
    cima
    #
    @88
    @200
    @209
    @162
    cP
    wss
    #
    @197
    @203
    @217
    wcel
    @212
    @159
    @218
    @196
    @197
    @195
    ad2antrr
    #
    @199
    @197
    simpr
    #
    cP
    @162
    @121
    @73
    fnfvima
    syl3anc
    @200
    @55
    @186
    @217
    @88
    wceq
    @215
    @200
    @88
    cB
    @200
    @153
    @154
    @216
    simprd
    elpwid
    cB
    cP
    @88
    cF
    f1imacnv
    syl2anc
    eleqtrd
    @158
    @90
    @196
    @197
    simpllr
    @87
    @207
    @201
    @86
    wcel
    vx
    vy
    @201
    @203
    @89
    @88
    @3
    @201
    @86
    eleq1
    @6
    @203
    wceq
    @86
    @206
    @201
    @6
    @203
    @76
    cJ
    oveq2
    eleq2d
    rspc2va
    syl21anc
    @200
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @76
    @203
    @201
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @211
    @200
    @43
    wph
    @46
    wph
    @155
    @157
    @90
    @196
    @197
    @43
    simp-6l
    f1otrkg.1
    sylancom
    @200
    @49
    wph
    @50
    wph
    @155
    @157
    @90
    @196
    @197
    @49
    simp-6l
    f1otrkg.2
    sylancom
    @156
    @157
    @90
    @196
    @197
    simp-4r
    @200
    @31
    @73
    cP
    wcel
    #
    @203
    cB
    wcel
    @211
    @200
    @162
    cP
    @73
    @219
    @220
    sseldd
    #
    cB
    cP
    @73
    cF
    f1ocnvdm
    syl2anc
    @200
    @31
    @70
    cP
    wcel
    #
    @201
    cB
    wcel
    @211
    @200
    @163
    cP
    @70
    @213
    @214
    sseldd
    #
    cB
    cP
    @70
    cF
    f1ocnvdm
    syl2anc
    f1otrgitv
    mpbid
    @200
    @31
    @223
    @202
    @70
    wceq
    @211
    @224
    cB
    cP
    @70
    cF
    f1ocnvfv2
    syl2anc
    @200
    @204
    @73
    @190
    cI
    @200
    @31
    @221
    @204
    @73
    wceq
    @211
    @222
    cB
    cP
    @73
    cF
    f1ocnvfv2
    syl2anc
    oveq2d
    3eltr3d
    3impa
    axtgcont
    r19.29a
    r19.29an
    ex
    ralrimivva
    3jca
    vx
    vy
    vz
    vv
    vu
    vt
    cB
    cH
    cJ
    cE
    vs
    va
    vb
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    istrkgb
    sylanbrc
    elind
    wph
    cstrkgcb
    @8
    cH
    wph
    @10
    @3
    @6
    wne
    #
    @6
    @71
    wcel
    #
    @92
    @76
    @110
    cJ
    co
    wcel
    #
    w3a
    #
    @11
    @76
    @92
    cE
    co
    #
    wceq
    #
    @6
    @5
    cE
    co
    #
    @92
    @110
    cE
    co
    #
    wceq
    #
    wa
    #
    @3
    @70
    cE
    co
    #
    @76
    @73
    cE
    co
    #
    wceq
    #
    @6
    @70
    cE
    co
    #
    @92
    @73
    cE
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    wa
    #
    @5
    @70
    cE
    co
    #
    @110
    @73
    cE
    co
    #
    wceq
    #
    wi
    #
    vv
    cB
    wral
    #
    vc
    cB
    wral
    #
    vb
    cB
    wral
    #
    va
    cB
    wral
    #
    vu
    cB
    wral
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    @226
    @231
    @229
    wceq
    #
    wa
    #
    vz
    cB
    wrex
    #
    vb
    cB
    wral
    va
    cB
    wral
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    wa
    cH
    cstrkgcb
    wcel
    wph
    @10
    @255
    @260
    @20
    wph
    @254
    vx
    cB
    wph
    @21
    wa
    #
    @253
    vy
    cB
    @261
    @22
    wa
    #
    @252
    vz
    cB
    @262
    @52
    wa
    #
    @251
    vu
    cB
    @263
    @105
    wa
    #
    @250
    va
    cB
    @264
    @157
    wa
    #
    @249
    vb
    cB
    @265
    @92
    cB
    wcel
    #
    wa
    #
    @248
    vc
    cB
    @267
    @110
    cB
    wcel
    #
    wa
    #
    @247
    vv
    cB
    @269
    @106
    wa
    #
    @243
    @246
    @270
    @243
    wa
    #
    @60
    @111
    cD
    co
    @110
    cF
    cfv
    #
    @114
    cD
    co
    @244
    @245
    @271
    @190
    @92
    cF
    cfv
    #
    @272
    cP
    @111
    cG
    cI
    cD
    @114
    @25
    @26
    @60
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    wph
    @28
    @21
    @22
    @52
    @105
    @157
    @266
    @268
    @106
    @243
    f1otrg.g
    ad9antr
    @271
    cB
    cP
    @3
    cF
    wph
    @30
    @21
    @22
    @52
    @105
    @157
    @266
    @268
    @106
    @243
    @33
    ad9antr
    #
    wph
    @21
    @22
    @52
    @105
    @157
    @266
    @268
    @106
    @243
    simp-9r
    #
    ffvelrnd
    @271
    cB
    cP
    @6
    cF
    @274
    @261
    @22
    @52
    @105
    @157
    @266
    @268
    @106
    @243
    simp-8r
    #
    ffvelrnd
    @271
    cB
    cP
    @5
    cF
    @274
    @262
    @52
    @105
    @157
    @266
    @268
    @106
    @243
    simp-7r
    #
    ffvelrnd
    @271
    cB
    cP
    @76
    cF
    @274
    @264
    @157
    @266
    @268
    @106
    @243
    simp-5r
    #
    ffvelrnd
    @271
    cB
    cP
    @92
    cF
    @274
    @265
    @266
    @268
    @106
    @243
    simp-4r
    #
    ffvelrnd
    @271
    cB
    cP
    @110
    cF
    @274
    @267
    @268
    @106
    @243
    simpllr
    #
    ffvelrnd
    @271
    cB
    cP
    @70
    cF
    @274
    @263
    @105
    @157
    @266
    @268
    @106
    @243
    simp-6r
    #
    ffvelrnd
    @271
    cB
    cP
    @73
    cF
    @274
    @269
    @106
    @243
    simplr
    #
    ffvelrnd
    @271
    @31
    @21
    wa
    #
    @22
    @225
    @25
    @26
    wne
    #
    @271
    @31
    @21
    wph
    @31
    @21
    @22
    @52
    @105
    @157
    @266
    @268
    @106
    @243
    f1otrkg.f
    ad9antr
    #
    @275
    jca
    @276
    @225
    @226
    @227
    @242
    @270
    simprl1
    @283
    @22
    wa
    #
    @225
    @284
    @286
    @25
    @26
    @3
    @6
    @283
    @56
    @17
    wi
    #
    vy
    cB
    @31
    @287
    vy
    cB
    wral
    #
    vx
    cB
    @31
    @180
    @192
    @288
    vx
    cB
    wral
    vx
    vy
    cB
    cP
    cF
    dff1o6
    simp3bi
    r19.21bi
    r19.21bi
    necon3d
    imp
    syl21anc
    @271
    @226
    @26
    @152
    wcel
    @225
    @226
    @227
    @242
    @270
    simprl2
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @3
    @5
    @6
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @271
    @43
    @46
    wph
    @43
    @46
    wi
    @21
    @22
    @52
    @105
    @157
    @266
    @268
    @106
    @243
    wph
    @43
    @46
    f1otrkg.1
    ex
    ad9antr
    imp
    #
    @271
    @49
    @50
    wph
    @49
    @50
    wi
    @21
    @22
    @52
    @105
    @157
    @266
    @268
    @106
    @243
    wph
    @49
    @50
    f1otrkg.2
    ex
    ad9antr
    imp
    #
    @275
    @277
    @276
    f1otrgitv
    mpbid
    @271
    @227
    @273
    @190
    @272
    cI
    co
    wcel
    @225
    @226
    @227
    @242
    @270
    simprl3
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @76
    @110
    @92
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @278
    @280
    @279
    f1otrgitv
    mpbid
    @271
    @11
    @229
    @27
    @190
    @273
    cD
    co
    #
    @271
    @230
    @233
    @271
    @234
    @241
    @270
    @228
    @242
    simprr
    #
    simpld
    #
    simpld
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @3
    @6
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @275
    @276
    f1otrgds
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @76
    @92
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @278
    @279
    f1otrgds
    3eqtr3d
    @271
    @231
    @232
    @26
    @60
    cD
    co
    @273
    @272
    cD
    co
    @271
    @230
    @233
    @293
    simprd
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @6
    @5
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @276
    @277
    f1otrgds
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @92
    @110
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @279
    @280
    f1otrgds
    3eqtr3d
    @271
    @235
    @236
    @25
    @111
    cD
    co
    @190
    @114
    cD
    co
    @271
    @237
    @240
    @271
    @234
    @241
    @292
    simprd
    #
    simpld
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @3
    @70
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @275
    @281
    f1otrgds
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @76
    @73
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @278
    @282
    f1otrgds
    3eqtr3d
    @271
    @238
    @239
    @26
    @111
    cD
    co
    @273
    @114
    cD
    co
    @271
    @237
    @240
    @294
    simprd
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @6
    @70
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @276
    @281
    f1otrgds
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @92
    @73
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @279
    @282
    f1otrgds
    3eqtr3d
    axtg5seg
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @5
    @70
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @277
    @281
    f1otrgds
    @271
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @110
    @73
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @285
    @289
    @290
    @280
    @282
    f1otrgds
    3eqtr4d
    ex
    ralrimiva
    ralrimiva
    ralrimiva
    ralrimiva
    ralrimiva
    ralrimiva
    ralrimiva
    ralrimiva
    wph
    @259
    vx
    vy
    cB
    cB
    @24
    @258
    va
    vb
    cB
    cB
    @24
    @157
    @266
    wa
    #
    wa
    #
    @26
    @25
    vw
    cv
    #
    cI
    co
    #
    wcel
    #
    @26
    @297
    cD
    co
    #
    @291
    wceq
    #
    wa
    #
    @258
    vw
    cP
    @296
    @297
    cP
    wcel
    #
    wa
    #
    @302
    wa
    #
    wph
    @303
    @6
    @3
    @297
    @121
    cfv
    #
    cJ
    co
    #
    wcel
    #
    @6
    @306
    cE
    co
    #
    @229
    wceq
    #
    @258
    wph
    @23
    @295
    @303
    @302
    simp-4l
    #
    @296
    @303
    @302
    simplr
    #
    @305
    @308
    @26
    @25
    @306
    cF
    cfv
    #
    cI
    co
    #
    wcel
    @305
    @26
    @298
    @314
    @304
    @299
    @301
    simprl
    @305
    @313
    @297
    @25
    cI
    @305
    @31
    @303
    @313
    @297
    wceq
    @305
    wph
    @31
    @311
    f1otrkg.f
    syl
    #
    @312
    cB
    cP
    @297
    cF
    f1ocnvfv2
    syl2anc
    #
    oveq2d
    eleqtrrd
    @305
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @3
    @306
    @6
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @315
    @305
    wph
    @43
    @46
    @311
    f1otrkg.1
    sylan
    #
    @305
    wph
    @49
    @50
    @311
    f1otrkg.2
    sylan
    #
    @24
    @21
    @295
    @303
    @302
    @35
    ad3antrrr
    @305
    wph
    @303
    @306
    cB
    wcel
    @311
    @312
    wph
    cP
    cB
    @297
    @121
    @129
    ffvelrnda
    #
    syl2anc
    #
    @24
    @22
    @295
    @303
    @302
    @37
    ad3antrrr
    #
    f1otrgitv
    mpbird
    @305
    @309
    @291
    @229
    @305
    @309
    @26
    @313
    cD
    co
    @300
    @291
    @305
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @6
    @306
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @315
    @317
    @318
    @321
    @320
    f1otrgds
    @305
    @313
    @297
    @26
    cD
    @316
    oveq2d
    @304
    @299
    @301
    simprr
    3eqtrd
    @305
    cB
    cD
    cP
    ve
    vf
    vg
    cE
    cF
    cG
    cH
    cI
    cJ
    @76
    @92
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @315
    @317
    @318
    @296
    @157
    @303
    @302
    @24
    @157
    @266
    simprl
    #
    ad2antrr
    @296
    @266
    @303
    @302
    @24
    @157
    @266
    simprr
    #
    ad2antrr
    f1otrgds
    eqtr4d
    wph
    @303
    wa
    #
    @308
    @310
    wa
    #
    @258
    @324
    @257
    @325
    vz
    @306
    cB
    @319
    @5
    @306
    wceq
    #
    @257
    @325
    wb
    @324
    @326
    @226
    @308
    @256
    @310
    @326
    @71
    @307
    @6
    @5
    @306
    @3
    cJ
    oveq2
    eleq2d
    @326
    @231
    @309
    @229
    @5
    @306
    @6
    cE
    oveq2
    eqeq1d
    anbi12d
    adantl
    rspcedv
    imp
    syl22anc
    @296
    vw
    @190
    @273
    cP
    cG
    cI
    cD
    @25
    @26
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    @24
    @28
    @295
    @29
    adantr
    @24
    @102
    @295
    @36
    adantr
    @24
    @103
    @295
    @38
    adantr
    @296
    cB
    cP
    @76
    cF
    @24
    @30
    @295
    @34
    adantr
    #
    @322
    ffvelrnd
    @296
    cB
    cP
    @92
    cF
    @327
    @323
    ffvelrnd
    axtgsegcon
    r19.29a
    ralrimivva
    ralrimivva
    jca32
    vx
    vy
    vz
    vv
    vu
    cB
    cH
    cJ
    cE
    va
    vb
    vc
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    istrkgcb
    sylibr
    wph
    @10
    cH
    clng
    cfv
    vx
    vy
    cB
    cB
    @4
    cdif
    @5
    @93
    wcel
    @3
    @5
    @6
    cJ
    co
    wcel
    @226
    w3o
    vz
    cB
    crab
    cmpt2
    wceq
    cH
    @8
    wcel
    @20
    f1otrg.l
    vx
    vy
    vz
    cB
    vf
    vi
    cH
    cJ
    cE
    vp
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    istrkgl
    sylanbrc
    elind
    elind
    vx
    vy
    vz
    vf
    vi
    vp
    df-trkg
    syl6eleqr
end
