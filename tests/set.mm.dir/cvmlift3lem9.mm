include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "ccom.mm"
include "wceq.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "cvmlift3lem8.mm"
include "cvmlift3lem5.mm"
include "cc0.mm"
include "c1.mm"
include "cii.mm"
include "crio.mm"
include "w3a.mm"
include "cicc.mm"
include "csn.mm"
include "cxp.mm"
include "ctopon.mm"
include "iitopon.mm"
include "a1i.mm"
include "ctop.mm"
include "csconn.mm"
include "sconntop.mm"
include "syl.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnconst2.mm"
include "syl3anc.mm"
include "0elunit.mm"
include "fvconst2g.mm"
include "sylancl.mm"
include "1elunit.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "wfn.mm"
include "ccvm.mm"
include "cuni.mm"
include "wf.mm"
include "cvmcn.mm"
include "eqid.mm"
include "cnf.mm"
include "ffn.mm"
include "4syl.mm"
include "fcoconst.mm"
include "syl2anc.mm"
include "3eqtr4d.mm"
include "wreu.mm"
include "wb.mm"
include "cvmtop1.mm"
include "cvmtop2.mm"
include "ffvelrnd.mm"
include "eqeltrd.mm"
include "fveq1d.mm"
include "3eqtr4rd.mm"
include "cvmlift.mm"
include "syl22anc.mm"
include "coeq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "anbi12d.mm"
include "riota2.mm"
include "mpbi2and.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "riotabidv.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "cvmlift3lem4.mm"
include "mpdan.mm"
include "mpbird.mm"
include "syl12anc.mm"

theorem cvmlift3lem9
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cO: class O
  let cY: class Y
  let vs: setvar s
  let vc: setvar c
  let vd: setvar d
  let vb: setvar b
  let vw: setvar w
  let cA: class A
  let cI: class I
  let va: setvar a
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vh: setvar h
  let vn: setvar n
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vt: setvar t
  let cQ: class Q
  let cR: class R
  let cX: class X
  let cT: class T
  let cZ: class Z
  let cW: class W
  assume cvmlift3.b: |- B = U. C
  assume cvmlift3.y: |- Y = U. K
  assume cvmlift3.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmlift3.k: |- ( ph -> K e. SConn )
  assume cvmlift3.l: |- ( ph -> K e. N-Locally PConn )
  assume cvmlift3.o: |- ( ph -> O e. Y )
  assume cvmlift3.g: |- ( ph -> G e. ( K Cn J ) )
  assume cvmlift3.p: |- ( ph -> P e. B )
  assume cvmlift3.e: |- ( ph -> ( F ` P ) = ( G ` O ) )
  assume cvmlift3.h: |- H = ( x e. Y |-> ( iota_ z e. B E. f e. ( II Cn K ) ( ( f ` 0 ) = O /\ ( f ` 1 ) = x /\ ( ( iota_ g e. ( II Cn C ) ( ( F o. g ) = ( G o. f ) /\ ( g ` 0 ) = P ) ) ` 1 ) = z ) ) )
  assume cvmlift3lem7.s: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. c e. s ( A. d e. ( s \ { c } ) ( c i^i d ) = (/) /\ ( F |` c ) e. ( ( C |`t c ) Homeo ( J |`t k ) ) ) ) } )

  disjoint c d
  disjoint c f
  disjoint c k
  disjoint c s
  disjoint c z
  disjoint d f
  disjoint d k
  disjoint d s
  disjoint d z
  disjoint f k
  disjoint f s
  disjoint f z
  disjoint k s
  disjoint k z
  disjoint s z
  disjoint f g
  disjoint g z
  disjoint c g
  disjoint c x
  disjoint J c
  disjoint d g
  disjoint d x
  disjoint J d
  disjoint f x
  disjoint J f
  disjoint g k
  disjoint g s
  disjoint g x
  disjoint J g
  disjoint k x
  disjoint J k
  disjoint s x
  disjoint J s
  disjoint J x
  disjoint F c
  disjoint F d
  disjoint F f
  disjoint F g
  disjoint F k
  disjoint F s
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint H c
  disjoint H d
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H z
  disjoint S f
  disjoint S x
  disjoint B d
  disjoint B f
  disjoint B g
  disjoint B x
  disjoint B z
  disjoint G c
  disjoint G d
  disjoint G f
  disjoint G g
  disjoint G k
  disjoint G x
  disjoint G z
  disjoint C c
  disjoint C d
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C s
  disjoint C x
  disjoint C z
  disjoint f ph
  disjoint ph x
  disjoint K c
  disjoint K f
  disjoint K g
  disjoint K x
  disjoint K z
  disjoint P c
  disjoint P d
  disjoint P f
  disjoint P g
  disjoint P x
  disjoint P z
  disjoint O c
  disjoint O f
  disjoint O g
  disjoint O x
  disjoint O z
  disjoint Y f
  disjoint Y g
  disjoint Y x
  disjoint Y z
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b k
  disjoint b s
  disjoint b w
  disjoint b z
  disjoint A b
  disjoint c w
  disjoint A c
  disjoint d w
  disjoint A d
  disjoint f w
  disjoint A f
  disjoint k w
  disjoint A k
  disjoint s w
  disjoint A s
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint I f
  disjoint g w
  disjoint I g
  disjoint I w
  disjoint I z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint J a
  disjoint b g
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint J b
  disjoint c u
  disjoint c v
  disjoint c y
  disjoint d u
  disjoint d v
  disjoint d y
  disjoint f u
  disjoint f v
  disjoint f y
  disjoint g u
  disjoint g v
  disjoint g y
  disjoint k u
  disjoint k v
  disjoint k y
  disjoint s u
  disjoint s v
  disjoint s y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint J u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint J v
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint x y
  disjoint J y
  disjoint a h
  disjoint a n
  disjoint a z
  disjoint F a
  disjoint b h
  disjoint b n
  disjoint F b
  disjoint c h
  disjoint c n
  disjoint d h
  disjoint d n
  disjoint f h
  disjoint f n
  disjoint g h
  disjoint g n
  disjoint h k
  disjoint h n
  disjoint h s
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint k n
  disjoint n s
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint u z
  disjoint F u
  disjoint v z
  disjoint F v
  disjoint F w
  disjoint y z
  disjoint F y
  disjoint M f
  disjoint M g
  disjoint M h
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint N f
  disjoint N g
  disjoint N w
  disjoint a m
  disjoint a t
  disjoint H a
  disjoint b m
  disjoint b t
  disjoint H b
  disjoint c m
  disjoint c t
  disjoint d m
  disjoint d t
  disjoint f m
  disjoint f t
  disjoint g m
  disjoint g t
  disjoint h m
  disjoint h t
  disjoint H h
  disjoint m n
  disjoint m t
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint H m
  disjoint n t
  disjoint H n
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint H t
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint Q f
  disjoint Q g
  disjoint Q w
  disjoint S a
  disjoint S b
  disjoint S m
  disjoint S t
  disjoint S v
  disjoint B a
  disjoint B b
  disjoint B h
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B y
  disjoint R g
  disjoint R w
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X d
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint X z
  disjoint G a
  disjoint G b
  disjoint G h
  disjoint k m
  disjoint k t
  disjoint m u
  disjoint G m
  disjoint G n
  disjoint t u
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint T s
  disjoint Z f
  disjoint Z g
  disjoint Z x
  disjoint Z z
  disjoint C a
  disjoint C b
  disjoint C h
  disjoint m s
  disjoint C m
  disjoint C n
  disjoint s t
  disjoint C t
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C y
  disjoint a ph
  disjoint h ph
  disjoint m ph
  disjoint n ph
  disjoint ph t
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint K a
  disjoint K b
  disjoint K h
  disjoint K m
  disjoint K n
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K y
  disjoint P a
  disjoint P b
  disjoint P h
  disjoint P n
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint O a
  disjoint O b
  disjoint O h
  disjoint O n
  disjoint O u
  disjoint O v
  disjoint O w
  disjoint Y a
  disjoint Y h
  disjoint Y m
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y y
  disjoint W c
  disjoint W d
  disjoint W f
  disjoint W h
  disjoint W n
  disjoint W x
  disjoint W y
  assert |- ( ph -> E. f e. ( K Cn C ) ( ( F o. f ) = G /\ ( f ` O ) = P ) )

  proof
    wph
    cH
    cK
    cC
    ccn
    co
    #
    wcel
    cF
    cH
    ccom
    #
    cG
    wceq
    #
    cO
    cH
    cfv
    #
    cP
    wceq
    #
    cF
    vf
    cv
    #
    ccom
    #
    cG
    wceq
    #
    cO
    @5
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vf
    @0
    wrex
    wph
    vx
    vz
    cB
    cC
    cP
    cS
    vf
    vg
    vk
    cF
    cG
    cH
    cJ
    cK
    cO
    cY
    vs
    vc
    vd
    cvmlift3.b
    cvmlift3.y
    cvmlift3.f
    cvmlift3.k
    cvmlift3.l
    cvmlift3.o
    cvmlift3.g
    cvmlift3.p
    cvmlift3.e
    cvmlift3.h
    cvmlift3lem7.s
    cvmlift3lem8
    wph
    vx
    vz
    cB
    cC
    cP
    vf
    vg
    cF
    cG
    cH
    cJ
    cK
    cO
    cY
    cvmlift3.b
    cvmlift3.y
    cvmlift3.f
    cvmlift3.k
    cvmlift3.l
    cvmlift3.o
    cvmlift3.g
    cvmlift3.p
    cvmlift3.e
    cvmlift3.h
    cvmlift3lem5
    wph
    @4
    cc0
    @5
    cfv
    #
    cO
    wceq
    #
    c1
    @5
    cfv
    #
    cO
    wceq
    #
    c1
    cF
    vg
    cv
    #
    ccom
    #
    cG
    @5
    ccom
    #
    wceq
    #
    cc0
    @15
    cfv
    #
    cP
    wceq
    #
    wa
    #
    vg
    cii
    cC
    ccn
    co
    #
    crio
    #
    cfv
    #
    cP
    wceq
    #
    w3a
    #
    vf
    cii
    cK
    ccn
    co
    #
    wrex
    #
    wph
    cc0
    c1
    cicc
    co
    #
    cO
    csn
    cxp
    #
    @27
    wcel
    #
    cc0
    @30
    cfv
    #
    cO
    wceq
    #
    c1
    @30
    cfv
    #
    cO
    wceq
    #
    c1
    @16
    cG
    @30
    ccom
    #
    wceq
    #
    @20
    wa
    #
    vg
    @22
    crio
    #
    cfv
    #
    cP
    wceq
    #
    @28
    wph
    cii
    @29
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
    cO
    cY
    wcel
    #
    @31
    @42
    wph
    iitopon
    a1i
    #
    wph
    cK
    ctop
    wcel
    #
    @43
    wph
    cK
    csconn
    wcel
    @46
    cvmlift3.k
    cK
    sconntop
    syl
    cK
    cY
    cvmlift3.y
    toptopon
    sylib
    cvmlift3.o
    cO
    cii
    cK
    @29
    cY
    cnconst2
    syl3anc
    wph
    @44
    cc0
    @29
    wcel
    #
    @33
    cvmlift3.o
    0elunit
    @29
    cO
    cc0
    cY
    fvconst2g
    sylancl
    wph
    @44
    c1
    @29
    wcel
    #
    @35
    cvmlift3.o
    1elunit
    @29
    cO
    c1
    cY
    fvconst2g
    sylancl
    wph
    @40
    c1
    @29
    cP
    csn
    cxp
    #
    cfv
    #
    cP
    wph
    c1
    @39
    @49
    wph
    cF
    @49
    ccom
    #
    @36
    wceq
    #
    cc0
    @49
    cfv
    #
    cP
    wceq
    #
    @39
    @49
    wceq
    #
    wph
    @29
    cP
    cF
    cfv
    #
    csn
    #
    cxp
    #
    @29
    cO
    cG
    cfv
    #
    csn
    #
    cxp
    #
    @51
    @36
    wph
    @57
    @60
    @29
    wph
    @56
    @59
    cvmlift3.e
    sneqd
    xpeq2d
    wph
    cF
    cB
    wfn
    #
    cP
    cB
    wcel
    #
    @51
    @58
    wceq
    wph
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cF
    cC
    cJ
    ccn
    co
    wcel
    cB
    cJ
    cuni
    #
    cF
    wf
    @62
    cvmlift3.f
    cC
    cF
    cJ
    cvmcn
    cF
    cC
    cJ
    cB
    @65
    cvmlift3.b
    @65
    eqid
    #
    cnf
    cB
    @65
    cF
    ffn
    4syl
    cvmlift3.p
    cF
    @29
    cB
    cP
    fcoconst
    syl2anc
    wph
    cG
    cY
    wfn
    #
    @44
    @36
    @61
    wceq
    wph
    cY
    @65
    cG
    wf
    #
    @67
    wph
    cG
    cK
    cJ
    ccn
    co
    wcel
    @68
    cvmlift3.g
    cG
    cK
    cJ
    cY
    @65
    cvmlift3.y
    @66
    cnf
    syl
    #
    cY
    @65
    cG
    ffn
    syl
    cvmlift3.o
    cG
    @29
    cY
    cO
    fcoconst
    syl2anc
    #
    3eqtr4d
    wph
    @63
    @47
    @54
    cvmlift3.p
    0elunit
    @29
    cP
    cc0
    cB
    fvconst2g
    sylancl
    wph
    @49
    @22
    wcel
    #
    @38
    vg
    @22
    wreu
    #
    @52
    @54
    wa
    #
    @55
    wb
    wph
    @42
    cC
    cB
    ctopon
    cfv
    wcel
    #
    @63
    @71
    @45
    wph
    cC
    ctop
    wcel
    #
    @74
    wph
    @64
    @75
    cvmlift3.f
    cC
    cF
    cJ
    cvmtop1
    syl
    cC
    cB
    cvmlift3.b
    toptopon
    sylib
    cvmlift3.p
    cP
    cii
    cC
    @29
    cB
    cnconst2
    syl3anc
    wph
    @64
    @36
    cii
    cJ
    ccn
    co
    #
    wcel
    @63
    @56
    cc0
    @36
    cfv
    #
    wceq
    @72
    cvmlift3.f
    wph
    @36
    @61
    @76
    @70
    wph
    @42
    cJ
    @65
    ctopon
    cfv
    wcel
    #
    @59
    @65
    wcel
    #
    @61
    @76
    wcel
    @45
    wph
    cJ
    ctop
    wcel
    #
    @78
    wph
    @64
    @80
    cvmlift3.f
    cC
    cF
    cJ
    cvmtop2
    syl
    cJ
    @65
    @66
    toptopon
    sylib
    wph
    cY
    @65
    cO
    cG
    @69
    cvmlift3.o
    ffvelrnd
    #
    @59
    cii
    cJ
    @29
    @65
    cnconst2
    syl3anc
    eqeltrd
    cvmlift3.p
    wph
    cc0
    @61
    cfv
    #
    @59
    @77
    @56
    wph
    @79
    @47
    @82
    @59
    wceq
    @81
    0elunit
    @29
    @59
    cc0
    @65
    fvconst2g
    sylancl
    wph
    cc0
    @36
    @61
    @70
    fveq1d
    cvmlift3.e
    3eqtr4rd
    cB
    cC
    cP
    vg
    cF
    @36
    cJ
    cvmlift3.b
    cvmlift
    syl22anc
    @38
    @73
    vg
    @22
    @49
    @15
    @49
    wceq
    #
    @37
    @52
    @20
    @54
    @83
    @16
    @51
    @36
    @15
    @49
    cF
    coeq2
    eqeq1d
    @83
    @19
    @53
    cP
    cc0
    @15
    @49
    fveq1
    eqeq1d
    anbi12d
    riota2
    syl2anc
    mpbi2and
    fveq1d
    wph
    @63
    @48
    @50
    cP
    wceq
    cvmlift3.p
    1elunit
    @29
    cP
    c1
    cB
    fvconst2g
    sylancl
    eqtrd
    @26
    @33
    @35
    @41
    w3a
    vf
    @30
    @27
    @5
    @30
    wceq
    #
    @12
    @33
    @14
    @35
    @25
    @41
    @84
    @11
    @32
    cO
    cc0
    @5
    @30
    fveq1
    eqeq1d
    @84
    @13
    @34
    cO
    c1
    @5
    @30
    fveq1
    eqeq1d
    @84
    @24
    @40
    cP
    @84
    c1
    @23
    @39
    @84
    @21
    @38
    vg
    @22
    @84
    @18
    @37
    @20
    @84
    @17
    @36
    @16
    @5
    @30
    cG
    coeq2
    eqeq2d
    anbi1d
    riotabidv
    fveq1d
    eqeq1d
    3anbi123d
    rspcev
    syl13anc
    wph
    @44
    @4
    @28
    wb
    cvmlift3.o
    wph
    vx
    vz
    cP
    cB
    cC
    cP
    vf
    vg
    cF
    cG
    cH
    cJ
    cK
    cO
    cO
    cY
    cvmlift3.b
    cvmlift3.y
    cvmlift3.f
    cvmlift3.k
    cvmlift3.l
    cvmlift3.o
    cvmlift3.g
    cvmlift3.p
    cvmlift3.e
    cvmlift3.h
    cvmlift3lem4
    mpdan
    mpbird
    @10
    @2
    @4
    wa
    vf
    cH
    @0
    @5
    cH
    wceq
    #
    @7
    @2
    @9
    @4
    @85
    @6
    @1
    cG
    @5
    cH
    cF
    coeq2
    eqeq1d
    @85
    @8
    @3
    cP
    cO
    @5
    cH
    fveq1
    eqeq1d
    anbi12d
    rspcev
    syl12anc
end
