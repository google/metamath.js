include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "cfv.mm"
include "wral.mm"
include "cvmlift3lem3.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wrex.mm"
include "ccvm.mm"
include "cuni.mm"
include "adantr.mm"
include "eqid.mm"
include "cnf.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "cvmcov.mm"
include "syl2anc.mm"
include "wex.mm"
include "n0.mm"
include "wss.mm"
include "crest.mm"
include "cpconn.mm"
include "w3a.mm"
include "ccnv.mm"
include "cima.mm"
include "cpw.mm"
include "cnlly.mm"
include "ad2antrr.mm"
include "simprr.mm"
include "cvmsrcl.mm"
include "cnima.mm"
include "simplr.mm"
include "simprl.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "4syl.mm"
include "mpbir2and.mm"
include "nlly2i.mm"
include "syl3anc.mm"
include "crio.mm"
include "ad3antrrr.mm"
include "csconn.mm"
include "wceq.mm"
include "simprll.mm"
include "elpwid.mm"
include "simprr3.mm"
include "simprlr.mm"
include "simprr2.mm"
include "simprr1.mm"
include "cvmlift3lem7.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "mpd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "rexlimdvw.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "ctop.mm"
include "sconntop.mm"
include "toptopon.mm"
include "sylib.mm"
include "cvmtop1.mm"
include "cncnp.mm"

theorem cvmlift3lem8
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
  assert |- ( ph -> H e. ( K Cn C ) )

  proof
    wph
    cH
    cK
    cC
    ccn
    co
    wcel
    #
    cY
    cB
    cH
    wf
    #
    cH
    vy
    cv
    #
    cK
    cC
    ccnp
    co
    cfv
    wcel
    #
    vy
    cY
    wral
    #
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
    cvmlift3lem3
    wph
    @3
    vy
    cY
    wph
    @2
    cY
    wcel
    #
    wa
    #
    @2
    cG
    cfv
    #
    va
    cv
    #
    wcel
    #
    @8
    cS
    cfv
    #
    c0
    wne
    #
    wa
    #
    va
    cJ
    wrex
    #
    @3
    @6
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @7
    cJ
    cuni
    #
    wcel
    @13
    wph
    @14
    @5
    cvmlift3.f
    adantr
    wph
    cY
    @15
    @2
    cG
    wph
    cG
    cK
    cJ
    ccn
    co
    wcel
    #
    cY
    @15
    cG
    wf
    #
    cvmlift3.g
    cG
    cK
    cJ
    cY
    @15
    cvmlift3.y
    @15
    eqid
    #
    cnf
    #
    syl
    ffvelrnda
    va
    vd
    vc
    cC
    @7
    cS
    vk
    cF
    cJ
    @15
    vs
    cvmlift3lem7.s
    @18
    cvmcov
    syl2anc
    @6
    @12
    @3
    va
    cJ
    @6
    @9
    @11
    @3
    @11
    vt
    cv
    #
    @10
    wcel
    #
    vt
    wex
    @6
    @9
    wa
    #
    @3
    vt
    @10
    n0
    @22
    @21
    @3
    vt
    @6
    @9
    @21
    @3
    @6
    @9
    @21
    wa
    #
    wa
    #
    @2
    vv
    cv
    #
    wcel
    #
    @25
    vm
    cv
    #
    wss
    #
    cK
    @27
    crest
    co
    cpconn
    wcel
    #
    w3a
    #
    vv
    cK
    wrex
    vm
    cG
    ccnv
    @8
    cima
    #
    cpw
    #
    wrex
    #
    @3
    @24
    cK
    cpconn
    cnlly
    wcel
    #
    @31
    cK
    wcel
    #
    @2
    @31
    wcel
    #
    @33
    wph
    @34
    @5
    @23
    cvmlift3.l
    ad2antrr
    @24
    @16
    @8
    cJ
    wcel
    #
    @35
    wph
    @16
    @5
    @23
    cvmlift3.g
    ad2antrr
    #
    @24
    @21
    @37
    @6
    @9
    @21
    simprr
    #
    vd
    vc
    cC
    cS
    @20
    @8
    vk
    cF
    cJ
    vs
    cvmlift3lem7.s
    cvmsrcl
    syl
    @8
    cG
    cK
    cJ
    cnima
    syl2anc
    @24
    @36
    @5
    @9
    wph
    @5
    @23
    simplr
    @6
    @9
    @21
    simprl
    #
    @24
    @16
    @17
    cG
    cY
    wfn
    @36
    @5
    @9
    wa
    wb
    @38
    @19
    cY
    @15
    cG
    ffn
    cY
    @2
    @8
    cG
    elpreima
    4syl
    mpbir2and
    vv
    cpconn
    @2
    @31
    cK
    vm
    nlly2i
    syl3anc
    @24
    @30
    @3
    vm
    vv
    @32
    cK
    @24
    @27
    @32
    wcel
    #
    @25
    cK
    wcel
    #
    wa
    #
    @30
    @3
    @24
    @43
    @30
    wa
    #
    wa
    #
    vx
    vz
    @8
    cB
    cC
    cP
    cS
    @20
    vf
    vg
    vk
    cF
    cG
    cH
    cJ
    cK
    @27
    cO
    @25
    @2
    cH
    cfv
    vb
    cv
    wcel
    vb
    @20
    crio
    #
    @2
    cY
    vs
    vb
    vc
    vd
    cvmlift3.b
    cvmlift3.y
    wph
    @14
    @5
    @23
    @44
    cvmlift3.f
    ad3antrrr
    wph
    cK
    csconn
    wcel
    #
    @5
    @23
    @44
    cvmlift3.k
    ad3antrrr
    wph
    @34
    @5
    @23
    @44
    cvmlift3.l
    ad3antrrr
    wph
    cO
    cY
    wcel
    @5
    @23
    @44
    cvmlift3.o
    ad3antrrr
    wph
    @16
    @5
    @23
    @44
    cvmlift3.g
    ad3antrrr
    wph
    cP
    cB
    wcel
    @5
    @23
    @44
    cvmlift3.p
    ad3antrrr
    wph
    cP
    cF
    cfv
    cO
    cG
    cfv
    wceq
    @5
    @23
    @44
    cvmlift3.e
    ad3antrrr
    cvmlift3.h
    cvmlift3lem7.s
    @24
    @9
    @44
    @40
    adantr
    @24
    @21
    @44
    @39
    adantr
    @45
    @27
    @31
    @24
    @41
    @42
    @30
    simprll
    elpwid
    @46
    eqid
    @26
    @28
    @29
    @43
    @24
    simprr3
    @24
    @41
    @42
    @30
    simprlr
    @26
    @28
    @29
    @43
    @24
    simprr2
    @26
    @28
    @29
    @43
    @24
    simprr1
    cvmlift3lem7
    expr
    rexlimdvva
    mpd
    expr
    exlimdv
    syl5bi
    expimpd
    rexlimdvw
    mpd
    ralrimiva
    wph
    cK
    cY
    ctopon
    cfv
    wcel
    #
    cC
    cB
    ctopon
    cfv
    wcel
    #
    @0
    @1
    @4
    wa
    wb
    wph
    cK
    ctop
    wcel
    #
    @48
    wph
    @47
    @50
    cvmlift3.k
    cK
    sconntop
    syl
    cK
    cY
    cvmlift3.y
    toptopon
    sylib
    wph
    cC
    ctop
    wcel
    #
    @49
    wph
    @14
    @51
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
    vy
    cH
    cK
    cC
    cY
    cB
    cncnp
    syl2anc
    mpbir2and
end
