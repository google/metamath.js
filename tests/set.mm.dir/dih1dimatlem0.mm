include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "ccom.mm"
include "wrex.mm"
include "simprl.mm"
include "simpl1.mm"
include "simprr.mm"
include "wbr.mm"
include "wn.mm"
include "lhpocnel2.mm"
include "syl.mm"
include "simpl2r.mm"
include "simpl3.mm"
include "tendoinvcl.mm"
include "simpld.mm"
include "syl3anc.mm"
include "simpl2l.mm"
include "tendocl.mm"
include "ltrnel.mm"
include "ltrniotacl.mm"
include "eqeltrd.mm"
include "tendococl.mm"
include "simp1.mm"
include "3ad2ant1.mm"
include "3adant2l.mm"
include "simp2l.mm"
include "ltrniotaval.mm"
include "cdlemd.mm"
include "syl311anc.mm"
include "adantr.mm"
include "fveq2d.mm"
include "tendocoval.mm"
include "syl121anc.mm"
include "3eqtr4d.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "tendolinv.mm"
include "coeq2d.mm"
include "tendo1mulr.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "syl5req.mm"
include "fveq1.mm"
include "eqeq2d.mm"
include "coeq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "jca31.mm"
include "simp3r.mm"
include "fveq1d.mm"
include "simp1l1.mm"
include "simp2.mm"
include "simp1l3.mm"
include "tendorinv.mm"
include "syl5eq.mm"
include "3eqtr2rd.mm"
include "simp3l.mm"
include "rexlimdv3a.mm"
include "impr.mm"
include "simprlr.mm"
include "jca.mm"
include "impbida.mm"

theorem dih1dimatlem0
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let c.x: class .x.
  let cU: class U
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  let vp: setvar p
  let vv: setvar v
  let vg: setvar g
  let vr: setvar r
  let vu: setvar u
  let cD: class D
  assume dih1dimat.h: |- H = ( LHyp ` K )
  assume dih1dimat.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih1dimat.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih1dimat.a: |- A = ( LSAtoms ` U )
  assume dih1dimat.b: |- B = ( Base ` K )
  assume dih1dimat.l: |- .<_ = ( le ` K )
  assume dih1dimat.c: |- C = ( Atoms ` K )
  assume dih1dimat.p: |- P = ( ( oc ` K ) ` W )
  assume dih1dimat.t: |- T = ( ( LTrn ` K ) ` W )
  assume dih1dimat.r: |- R = ( ( trL ` K ) ` W )
  assume dih1dimat.e: |- E = ( ( TEndo ` K ) ` W )
  assume dih1dimat.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dih1dimat.d: |- F = ( Scalar ` U )
  assume dih1dimat.j: |- J = ( invr ` F )
  assume dih1dimat.v: |- V = ( Base ` U )
  assume dih1dimat.m: |- .x. = ( .s ` U )
  assume dih1dimat.s: |- S = ( LSubSp ` U )
  assume dih1dimat.n: |- N = ( LSpan ` U )
  assume dih1dimat.z: |- .0. = ( 0g ` U )
  assume dih1dimat.g: |- G = ( iota_ h e. T ( h ` P ) = ( ( ( J ` s ) ` f ) ` P ) )

  disjoint .<_ h
  disjoint B h
  disjoint f i
  disjoint f p
  disjoint f s
  disjoint f t
  disjoint E f
  disjoint i p
  disjoint i s
  disjoint i t
  disjoint E i
  disjoint p s
  disjoint p t
  disjoint E p
  disjoint s t
  disjoint E s
  disjoint E t
  disjoint F t
  disjoint C h
  disjoint G i
  disjoint G p
  disjoint G t
  disjoint h t
  disjoint J h
  disjoint J t
  disjoint N f
  disjoint N s
  disjoint N t
  disjoint f h
  disjoint K f
  disjoint h i
  disjoint h p
  disjoint h s
  disjoint K h
  disjoint K i
  disjoint K p
  disjoint K s
  disjoint K t
  disjoint T f
  disjoint T h
  disjoint T i
  disjoint T p
  disjoint T s
  disjoint T t
  disjoint U f
  disjoint U h
  disjoint U s
  disjoint U t
  disjoint H f
  disjoint H h
  disjoint H i
  disjoint H p
  disjoint H s
  disjoint H t
  disjoint V f
  disjoint V i
  disjoint V p
  disjoint V s
  disjoint V t
  disjoint W f
  disjoint W h
  disjoint W i
  disjoint W p
  disjoint W s
  disjoint W t
  disjoint I f
  disjoint I s
  disjoint O i
  disjoint O p
  disjoint O t
  disjoint P h
  disjoint .x. t
  disjoint .0. v
  disjoint f g
  disjoint f r
  disjoint f u
  disjoint f v
  disjoint g i
  disjoint g p
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint E g
  disjoint i r
  disjoint i u
  disjoint i v
  disjoint p r
  disjoint p u
  disjoint p v
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint E r
  disjoint s u
  disjoint s v
  disjoint t u
  disjoint t v
  disjoint u v
  disjoint E u
  disjoint E v
  disjoint F u
  disjoint D v
  disjoint G g
  disjoint G r
  disjoint g h
  disjoint J g
  disjoint h r
  disjoint J r
  disjoint N u
  disjoint N v
  disjoint K g
  disjoint h u
  disjoint h v
  disjoint K r
  disjoint K u
  disjoint K v
  disjoint T g
  disjoint T u
  disjoint T v
  disjoint U u
  disjoint U v
  disjoint H u
  disjoint H v
  disjoint V u
  disjoint V v
  disjoint W g
  disjoint W r
  disjoint W u
  disjoint W v
  disjoint I v
  disjoint O u
  disjoint P g
  disjoint P r
  disjoint .x. u
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( f e. T /\ s e. E ) /\ s =/= O ) -> ( ( i = ( p ` G ) /\ p e. E ) <-> ( ( i e. T /\ p e. E ) /\ E. t e. E ( i = ( t ` f ) /\ p = ( t o. s ) ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vf
    cv
    #
    cT
    wcel
    #
    vs
    cv
    #
    cE
    wcel
    #
    wa
    #
    @3
    cO
    wne
    #
    w3a
    #
    vi
    cv
    #
    cG
    vp
    cv
    #
    cfv
    #
    wceq
    #
    @9
    cE
    wcel
    #
    wa
    #
    @8
    cT
    wcel
    #
    @12
    wa
    #
    @8
    @1
    vt
    cv
    #
    cfv
    #
    wceq
    #
    @9
    @16
    @3
    ccom
    #
    wceq
    #
    wa
    #
    vt
    cE
    wrex
    #
    wa
    #
    @7
    @13
    wa
    #
    @14
    @12
    @22
    @24
    @8
    @10
    cT
    @7
    @11
    @12
    simprl
    #
    @24
    @0
    @12
    cG
    cT
    wcel
    #
    @10
    cT
    wcel
    @0
    @5
    @6
    @13
    simpl1
    #
    @7
    @11
    @12
    simprr
    #
    @24
    @0
    cP
    cC
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cP
    @1
    @3
    cJ
    cfv
    #
    cfv
    #
    cfv
    #
    cC
    wcel
    @32
    cW
    c.le
    wbr
    wn
    wa
    #
    @26
    @27
    @24
    @0
    @29
    @27
    cC
    cP
    cH
    cK
    c.le
    cW
    dih1dimat.l
    dih1dimat.c
    dih1dimat.h
    dih1dimat.p
    lhpocnel2
    #
    syl
    #
    @24
    @0
    @31
    cT
    wcel
    #
    @29
    @33
    @27
    @24
    @0
    @30
    cE
    wcel
    #
    @2
    @36
    @27
    @24
    @0
    @4
    @6
    @37
    @27
    @2
    @4
    @0
    @6
    @13
    simpl2r
    #
    @0
    @5
    @6
    @13
    simpl3
    #
    @0
    @4
    @6
    w3a
    @37
    @30
    cO
    wne
    cB
    @3
    cT
    cU
    vh
    cE
    cF
    cH
    cK
    cJ
    cO
    cW
    dih1dimat.b
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    dih1dimat.o
    dih1dimat.u
    dih1dimat.d
    dih1dimat.j
    tendoinvcl
    simpld
    #
    syl3anc
    #
    @2
    @4
    @0
    @6
    @13
    simpl2l
    #
    @30
    cT
    cE
    @1
    cH
    cK
    chlt
    cW
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    tendocl
    #
    syl3anc
    @35
    cC
    cP
    cT
    @31
    cH
    cK
    c.le
    cW
    dih1dimat.l
    dih1dimat.c
    dih1dimat.h
    dih1dimat.t
    ltrnel
    #
    syl3anc
    cC
    cP
    @32
    cT
    vh
    cG
    cH
    cK
    c.le
    cW
    dih1dimat.l
    dih1dimat.c
    dih1dimat.h
    dih1dimat.t
    dih1dimat.g
    ltrniotacl
    #
    syl3anc
    @9
    cT
    cE
    cG
    cH
    cK
    chlt
    cW
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    tendocl
    syl3anc
    eqeltrd
    @28
    @24
    @9
    @30
    ccom
    #
    cE
    wcel
    #
    @8
    @1
    @46
    cfv
    #
    wceq
    #
    @9
    @46
    @3
    ccom
    #
    wceq
    #
    @22
    @24
    @0
    @12
    @37
    @47
    @27
    @28
    @41
    @9
    @30
    cE
    cH
    cK
    cW
    dih1dimat.h
    dih1dimat.e
    tendococl
    syl3anc
    @24
    @10
    @31
    @9
    cfv
    #
    @8
    @48
    @24
    cG
    @31
    @9
    @7
    cG
    @31
    wceq
    #
    @13
    @7
    @0
    @26
    @36
    @29
    cP
    cG
    cfv
    @32
    wceq
    #
    @53
    @0
    @5
    @6
    simp1
    #
    @7
    @0
    @29
    @33
    @26
    @55
    @0
    @5
    @29
    @6
    @34
    3ad2ant1
    #
    @7
    @0
    @36
    @29
    @33
    @55
    @7
    @0
    @37
    @2
    @36
    @55
    @0
    @4
    @6
    @37
    @2
    @40
    3adant2l
    @0
    @2
    @4
    @6
    simp2l
    @43
    syl3anc
    #
    @56
    @44
    syl3anc
    #
    @45
    syl3anc
    @57
    @56
    @7
    @0
    @29
    @33
    @54
    @55
    @56
    @58
    cC
    cP
    @32
    cT
    vh
    cG
    cH
    cK
    c.le
    cW
    dih1dimat.l
    dih1dimat.c
    dih1dimat.h
    dih1dimat.t
    dih1dimat.g
    ltrniotaval
    syl3anc
    cC
    cP
    cT
    cG
    @31
    cH
    cK
    c.le
    cW
    dih1dimat.l
    dih1dimat.c
    dih1dimat.h
    dih1dimat.t
    cdlemd
    syl311anc
    #
    adantr
    fveq2d
    @25
    @24
    @0
    @12
    @37
    @2
    @48
    @52
    wceq
    @27
    @28
    @41
    @42
    cT
    @9
    cE
    @1
    cH
    cK
    @30
    cW
    chlt
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    tendocoval
    syl121anc
    3eqtr4d
    @24
    @50
    @9
    @30
    @3
    ccom
    #
    ccom
    #
    @9
    @9
    @30
    @3
    coass
    @24
    @61
    @9
    cid
    cT
    cres
    #
    ccom
    #
    @9
    @24
    @60
    @62
    @9
    @24
    @0
    @4
    @6
    @60
    @62
    wceq
    @27
    @38
    @39
    cB
    @3
    cT
    cU
    vh
    cE
    cF
    cH
    cK
    cJ
    cO
    cW
    dih1dimat.b
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    dih1dimat.o
    dih1dimat.u
    dih1dimat.d
    dih1dimat.j
    tendolinv
    syl3anc
    coeq2d
    @24
    @0
    @12
    @63
    @9
    wceq
    @27
    @28
    cT
    @9
    cE
    cH
    cK
    cW
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    tendo1mulr
    syl2anc
    eqtrd
    syl5req
    @21
    @49
    @51
    wa
    vt
    @46
    cE
    @16
    @46
    wceq
    #
    @18
    @49
    @20
    @51
    @64
    @17
    @48
    @8
    @1
    @16
    @46
    fveq1
    eqeq2d
    @64
    @19
    @50
    @9
    @16
    @46
    @3
    coeq1
    eqeq2d
    anbi12d
    rspcev
    syl12anc
    jca31
    @7
    @23
    wa
    @11
    @12
    @7
    @15
    @22
    @11
    @7
    @15
    wa
    #
    @21
    @11
    vt
    cE
    @65
    @16
    cE
    wcel
    #
    @21
    w3a
    #
    @17
    @52
    @8
    @10
    @67
    @52
    @31
    @19
    cfv
    #
    @1
    @19
    @30
    ccom
    #
    cfv
    #
    @17
    @67
    @31
    @9
    @19
    @65
    @66
    @18
    @20
    simp3r
    fveq1d
    @67
    @0
    @19
    cE
    wcel
    #
    @37
    @2
    @70
    @68
    wceq
    @0
    @5
    @6
    @15
    @66
    @21
    simp1l1
    #
    @67
    @0
    @66
    @4
    @71
    @72
    @65
    @66
    @21
    simp2
    #
    @65
    @66
    @4
    @21
    @2
    @4
    @0
    @6
    @15
    simpl2r
    3ad2ant1
    #
    @16
    @3
    cE
    cH
    cK
    cW
    dih1dimat.h
    dih1dimat.e
    tendococl
    syl3anc
    @67
    @0
    @4
    @6
    @37
    @72
    @74
    @0
    @5
    @6
    @15
    @66
    @21
    simp1l3
    #
    @40
    syl3anc
    @65
    @66
    @2
    @21
    @2
    @4
    @0
    @6
    @15
    simpl2l
    3ad2ant1
    cT
    @19
    cE
    @1
    cH
    cK
    @30
    cW
    chlt
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    tendocoval
    syl121anc
    @67
    @1
    @69
    @16
    @67
    @69
    @16
    @3
    @30
    ccom
    #
    ccom
    #
    @16
    @16
    @3
    @30
    coass
    @67
    @77
    @16
    @62
    ccom
    #
    @16
    @67
    @76
    @62
    @16
    @67
    @0
    @4
    @6
    @76
    @62
    wceq
    @72
    @74
    @75
    cB
    @3
    cT
    cU
    vh
    cE
    cF
    cH
    cK
    cJ
    cO
    cW
    dih1dimat.b
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    dih1dimat.o
    dih1dimat.u
    dih1dimat.d
    dih1dimat.j
    tendorinv
    syl3anc
    coeq2d
    @67
    @0
    @66
    @78
    @16
    wceq
    @72
    @73
    cT
    @16
    cE
    cH
    cK
    cW
    dih1dimat.h
    dih1dimat.t
    dih1dimat.e
    tendo1mulr
    syl2anc
    eqtrd
    syl5eq
    fveq1d
    3eqtr2rd
    @65
    @66
    @18
    @20
    simp3l
    @67
    cG
    @31
    @9
    @65
    @66
    @53
    @21
    @7
    @53
    @15
    @59
    adantr
    3ad2ant1
    fveq2d
    3eqtr4d
    rexlimdv3a
    impr
    @7
    @14
    @12
    @22
    simprlr
    jca
    impbida
end
