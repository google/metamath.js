include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wne.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cstrkge.mm"
include "elex.mm"
include "syl.mm"
include "wa.mm"
include "cfv.mm"
include "ccnv.mm"
include "wf.mm"
include "wf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "ad6antr.mm"
include "simpllr.mm"
include "ffvelrnd.mm"
include "simplr.mm"
include "simpr1.mm"
include "wceq.mm"
include "ad3antrrr.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "simp-4l.mm"
include "simplll.mm"
include "adantlr.mm"
include "sylancom.mm"
include "wb.mm"
include "simprl.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "f1otrgitv.mm"
include "mpbird.mm"
include "simpr2.mm"
include "simplr1.mm"
include "simpr3.mm"
include "oveq12d.mm"
include "simplr3.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "3anbi13d.mm"
include "3anbi23d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "adantr.mm"
include "simplr2.mm"
include "mpbid.mm"
include "jca.mm"
include "wfn.mm"
include "crn.mm"
include "dff1o6.mm"
include "simp3bi.mm"
include "r19.21bi.mm"
include "necon3d.mm"
include "imp.mm"
include "syl21anc.mm"
include "axtgeucl.mm"
include "r19.29vva.mm"
include "ex.mm"
include "ralrimivvva.mm"
include "ralrimivva.mm"
include "istrkge.mm"
include "sylanbrc.mm"

theorem f1otrge
  let wph: wff ph
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
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  assume f1otrge.g: |- ( ph -> G e. TarskiGE )

  disjoint e f
  disjoint e g
  disjoint B e
  disjoint f g
  disjoint B f
  disjoint B g
  disjoint D e
  disjoint D f
  disjoint D g
  disjoint E e
  disjoint E f
  disjoint E g
  disjoint F e
  disjoint F f
  disjoint F g
  disjoint I e
  disjoint I f
  disjoint I g
  disjoint J e
  disjoint J f
  disjoint J g
  disjoint P e
  disjoint P f
  disjoint P g
  disjoint e ph
  disjoint f ph
  disjoint g ph
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
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f i
  disjoint f p
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g i
  disjoint g p
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
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
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
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
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint I a
  disjoint I c
  disjoint I d
  disjoint I u
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
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
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P d
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint d ph
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint H i
  disjoint H p
  assert |- ( ph -> H e. TarskiGE )

  proof
    wph
    cH
    cvv
    wcel
    #
    vu
    cv
    #
    vx
    cv
    #
    vv
    cv
    #
    cJ
    co
    wcel
    #
    @1
    vy
    cv
    #
    vz
    cv
    #
    cJ
    co
    wcel
    #
    @2
    @1
    wne
    #
    w3a
    #
    @5
    @2
    va
    cv
    #
    cJ
    co
    #
    wcel
    #
    @6
    @2
    vb
    cv
    #
    cJ
    co
    #
    wcel
    #
    @3
    @10
    @13
    cJ
    co
    #
    wcel
    #
    w3a
    #
    vb
    cB
    wrex
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
    cH
    cstrkge
    wcel
    wph
    cH
    cV
    wcel
    @0
    f1otrg.h
    cH
    cV
    elex
    syl
    wph
    @21
    vx
    vy
    cB
    cB
    wph
    @2
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    #
    wa
    #
    @20
    vz
    vu
    vv
    cB
    cB
    cB
    @25
    @6
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    @3
    cB
    wcel
    #
    w3a
    #
    wa
    #
    @9
    @19
    @30
    @9
    wa
    #
    @5
    cF
    cfv
    #
    @2
    cF
    cfv
    #
    vc
    cv
    #
    cI
    co
    #
    wcel
    #
    @6
    cF
    cfv
    #
    @33
    vd
    cv
    #
    cI
    co
    #
    wcel
    #
    @3
    cF
    cfv
    #
    @34
    @38
    cI
    co
    #
    wcel
    #
    w3a
    #
    @19
    vc
    vd
    cP
    cP
    @31
    @34
    cP
    wcel
    #
    wa
    #
    @38
    cP
    wcel
    #
    wa
    #
    @44
    wa
    #
    @34
    cF
    ccnv
    #
    cfv
    #
    cB
    wcel
    @38
    @50
    cfv
    #
    cB
    wcel
    @5
    @2
    @51
    cJ
    co
    #
    wcel
    #
    @6
    @2
    @52
    cJ
    co
    #
    wcel
    #
    @3
    @51
    @52
    cJ
    co
    #
    wcel
    #
    @19
    @49
    cP
    cB
    @34
    @50
    wph
    cP
    cB
    @50
    wf
    #
    @24
    @29
    @9
    @45
    @47
    @44
    wph
    cB
    cP
    cF
    wf1o
    #
    cP
    cB
    @50
    wf1o
    @59
    f1otrkg.f
    cB
    cP
    cF
    f1ocnv
    cP
    cB
    @50
    f1of
    3syl
    ad6antr
    #
    @31
    @45
    @47
    @44
    simpllr
    #
    ffvelrnd
    #
    @49
    cP
    cB
    @38
    @50
    @61
    @46
    @47
    @44
    simplr
    #
    ffvelrnd
    #
    @49
    @54
    @32
    @33
    @51
    cF
    cfv
    #
    cI
    co
    #
    wcel
    @49
    @32
    @35
    @67
    @48
    @36
    @40
    @43
    simpr1
    @49
    @66
    @34
    @33
    cI
    @49
    @60
    @45
    @66
    @34
    wceq
    @31
    @60
    @45
    @47
    @44
    wph
    @60
    @24
    @29
    @9
    f1otrkg.f
    ad3antrrr
    #
    ad3antrrr
    #
    @62
    cB
    cP
    @34
    cF
    f1ocnvfv2
    syl2anc
    #
    oveq2d
    eleqtrrd
    @49
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
    @2
    @51
    @5
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @69
    @49
    ve
    cv
    #
    cB
    wcel
    #
    vf
    cv
    #
    cB
    wcel
    #
    wa
    #
    @31
    @71
    @73
    cE
    co
    @71
    cF
    cfv
    #
    @73
    cF
    cfv
    #
    cD
    co
    wceq
    #
    @31
    @45
    @47
    @44
    @75
    simp-4l
    @31
    @75
    @25
    @78
    @25
    @29
    @9
    @75
    simplll
    wph
    @75
    @78
    @24
    f1otrkg.1
    adantlr
    sylancom
    #
    sylancom
    #
    @49
    @72
    @74
    vg
    cv
    #
    cB
    wcel
    w3a
    #
    @31
    @81
    @71
    @73
    cJ
    co
    wcel
    @81
    cF
    cfv
    @76
    @77
    cI
    co
    wcel
    wb
    #
    @31
    @45
    @47
    @44
    @82
    simp-4l
    @31
    @82
    @25
    @83
    @25
    @29
    @9
    @82
    simplll
    wph
    @82
    @83
    @24
    f1otrkg.2
    adantlr
    sylancom
    #
    sylancom
    #
    @31
    @22
    @45
    @47
    @44
    @25
    @22
    @29
    @9
    wph
    @22
    @23
    simprl
    #
    ad2antrr
    #
    ad3antrrr
    #
    @63
    @31
    @23
    @45
    @47
    @44
    @25
    @23
    @29
    @9
    wph
    @22
    @23
    simprr
    #
    ad2antrr
    #
    ad3antrrr
    f1otrgitv
    mpbird
    @49
    @56
    @37
    @33
    @52
    cF
    cfv
    #
    cI
    co
    #
    wcel
    @49
    @37
    @39
    @92
    @48
    @36
    @40
    @43
    simpr2
    @49
    @91
    @38
    @33
    cI
    @49
    @60
    @47
    @91
    @38
    wceq
    @69
    @64
    cB
    cP
    @38
    cF
    f1ocnvfv2
    syl2anc
    #
    oveq2d
    eleqtrrd
    @49
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
    @2
    @52
    @6
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @69
    @80
    @85
    @88
    @65
    @31
    @26
    @45
    @47
    @44
    @26
    @27
    @28
    @25
    @9
    simplr1
    #
    ad3antrrr
    f1otrgitv
    mpbird
    @49
    @58
    @41
    @66
    @91
    cI
    co
    #
    wcel
    @49
    @41
    @42
    @95
    @48
    @36
    @40
    @43
    simpr3
    @49
    @66
    @34
    @91
    @38
    cI
    @70
    @93
    oveq12d
    eleqtrrd
    @49
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
    @51
    @52
    @3
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @69
    @80
    @85
    @63
    @65
    @31
    @28
    @45
    @47
    @44
    @26
    @27
    @28
    @25
    @9
    simplr3
    #
    ad3antrrr
    f1otrgitv
    mpbird
    @18
    @54
    @56
    @58
    w3a
    @54
    @15
    @3
    @51
    @13
    cJ
    co
    #
    wcel
    #
    w3a
    va
    vb
    @51
    @52
    cB
    cB
    @10
    @51
    wceq
    #
    @12
    @54
    @17
    @98
    @15
    @99
    @11
    @53
    @5
    @10
    @51
    @2
    cJ
    oveq2
    eleq2d
    @99
    @16
    @97
    @3
    @10
    @51
    @13
    cJ
    oveq1
    eleq2d
    3anbi13d
    @13
    @52
    wceq
    #
    @15
    @56
    @98
    @58
    @54
    @100
    @14
    @55
    @6
    @13
    @52
    @2
    cJ
    oveq2
    eleq2d
    @100
    @97
    @57
    @3
    @13
    @52
    @51
    cJ
    oveq2
    eleq2d
    3anbi23d
    rspc2ev
    syl113anc
    @31
    cP
    @1
    cF
    cfv
    #
    cG
    cI
    cD
    @41
    @33
    @32
    @37
    vc
    vd
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    wph
    cG
    cstrkge
    wcel
    @24
    @29
    @9
    f1otrge.g
    ad3antrrr
    @25
    @33
    cP
    wcel
    @29
    @9
    @25
    cB
    cP
    @2
    cF
    wph
    cB
    cP
    cF
    wf
    #
    @24
    wph
    @60
    @102
    f1otrkg.f
    cB
    cP
    cF
    f1of
    syl
    #
    adantr
    #
    @86
    ffvelrnd
    ad2antrr
    @25
    @32
    cP
    wcel
    @29
    @9
    @25
    cB
    cP
    @5
    cF
    @104
    @89
    ffvelrnd
    ad2antrr
    @31
    cB
    cP
    @6
    cF
    wph
    @102
    @24
    @29
    @9
    @103
    ad3antrrr
    #
    @94
    ffvelrnd
    @31
    cB
    cP
    @1
    cF
    @105
    @26
    @27
    @28
    @25
    @9
    simplr2
    #
    ffvelrnd
    @31
    cB
    cP
    @3
    cF
    @105
    @96
    ffvelrnd
    @31
    @4
    @101
    @33
    @41
    cI
    co
    wcel
    @30
    @4
    @7
    @8
    simpr1
    @31
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
    @2
    @3
    @1
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @68
    @79
    @84
    @87
    @96
    @106
    f1otrgitv
    mpbid
    @31
    @7
    @101
    @32
    @37
    cI
    co
    wcel
    @30
    @4
    @7
    @8
    simpr2
    @31
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
    @6
    @1
    f1otrkg.p
    f1otrkg.d
    f1otrkg.i
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    @68
    @79
    @84
    @90
    @94
    @106
    f1otrgitv
    mpbid
    @31
    @60
    @22
    wa
    #
    @27
    @8
    @33
    @101
    wne
    #
    @31
    @60
    @22
    @68
    @87
    jca
    @106
    @30
    @4
    @7
    @8
    simpr3
    @107
    @27
    wa
    #
    @8
    @108
    @109
    @33
    @101
    @2
    @1
    @107
    @33
    @101
    wceq
    @2
    @1
    wceq
    wi
    #
    vu
    cB
    @60
    @110
    vu
    cB
    wral
    #
    vx
    cB
    @60
    cF
    cB
    wfn
    cF
    crn
    cP
    wceq
    @111
    vx
    cB
    wral
    vx
    vu
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
    axtgeucl
    r19.29vva
    ex
    ralrimivvva
    ralrimivva
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
    f1otrkg.b
    f1otrkg.e
    f1otrkg.j
    istrkge
    sylanbrc
end
