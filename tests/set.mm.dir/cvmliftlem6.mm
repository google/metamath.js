include "wa.mm"
include "cfv.mm"
include "wf.mm"
include "ccom.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cdiv.mm"
include "wcel.mm"
include "c2nd.mm"
include "crio.mm"
include "ccnv.mm"
include "cmpt.mm"
include "cuni.mm"
include "wss.mm"
include "c1st.mm"
include "cfz.mm"
include "adantrr.mm"
include "cvmliftlem1.mm"
include "cvmsss.mm"
include "syl.mm"
include "ccvm.mm"
include "adantr.mm"
include "csn.mm"
include "cima.mm"
include "wfn.mm"
include "wb.mm"
include "ccn.mm"
include "cvmcn.mm"
include "cnf.mm"
include "3syl.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mpbid.mm"
include "simpld.mm"
include "simprd.mm"
include "cicc.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cr.mm"
include "cn.mm"
include "elfznn.mm"
include "nnred.mm"
include "peano2rem.mm"
include "nndivred.mm"
include "rexrd.mm"
include "clt.mm"
include "ltm1d.mm"
include "cc0.mm"
include "nngt0d.mm"
include "ltdiv1.mm"
include "syl112anc.mm"
include "ltled.mm"
include "lbicc2.mm"
include "syl3anc.mm"
include "syl6eleqr.mm"
include "cvmliftlem3.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "cvmsiota.mm"
include "syl13anc.mm"
include "sseldd.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "wf1o.mm"
include "cvmsf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "simprr.mm"
include "ffvelrnd.mm"
include "anassrs.mm"
include "fmptd.mm"
include "cvmliftlem5.mm"
include "syldan.mm"
include "feq1d.mm"
include "mpbird.mm"
include "fvres.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "3eqtr2rd.mm"
include "mpteq2dva.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "cii.mm"
include "iiuni.mm"
include "cvmliftlem2.mm"
include "fssresd.mm"
include "3eqtr4d.mm"
include "jca.mm"

theorem cvmliftlem6
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cG: class G
  let cJ: class J
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vb: setvar b
  let vy: setvar y
  let va: setvar a
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let vt: setvar t
  let vw: setvar w
  let cK: class K
  assume cvmliftlem.1: |- S = ( k e. J |-> { s e. ( ~P C \ { (/) } ) | ( U. s = ( `' F " k ) /\ A. u e. s ( A. v e. ( s \ { u } ) ( u i^i v ) = (/) /\ ( F |` u ) e. ( ( C |`t u ) Homeo ( J |`t k ) ) ) ) } )
  assume cvmliftlem.b: |- B = U. C
  assume cvmliftlem.x: |- X = U. J
  assume cvmliftlem.f: |- ( ph -> F e. ( C CovMap J ) )
  assume cvmliftlem.g: |- ( ph -> G e. ( II Cn J ) )
  assume cvmliftlem.p: |- ( ph -> P e. B )
  assume cvmliftlem.e: |- ( ph -> ( F ` P ) = ( G ` 0 ) )
  assume cvmliftlem.n: |- ( ph -> N e. NN )
  assume cvmliftlem.t: |- ( ph -> T : ( 1 ... N ) --> U_ j e. J ( { j } X. ( S ` j ) ) )
  assume cvmliftlem.a: |- ( ph -> A. k e. ( 1 ... N ) ( G " ( ( ( k - 1 ) / N ) [,] ( k / N ) ) ) C_ ( 1st ` ( T ` k ) ) )
  assume cvmliftlem.l: |- L = ( topGen ` ran (,) )
  assume cvmliftlem.q: |- Q = seq 0 ( ( x e. _V , m e. NN |-> ( z e. ( ( ( m - 1 ) / N ) [,] ( m / N ) ) |-> ( `' ( F |` ( iota_ b e. ( 2nd ` ( T ` m ) ) ( x ` ( ( m - 1 ) / N ) ) e. b ) ) ` ( G ` z ) ) ) ) , ( ( _I |` NN ) u. { <. 0 , { <. 0 , P >. } >. } ) )
  assume cvmliftlem5.3: |- W = ( ( ( M - 1 ) / N ) [,] ( M / N ) )
  assume cvmliftlem6.1: |- ( ( ph /\ ps ) -> M e. ( 1 ... N ) )
  assume cvmliftlem6.2: |- ( ( ph /\ ps ) -> ( ( Q ` ( M - 1 ) ) ` ( ( M - 1 ) / N ) ) e. ( `' F " { ( G ` ( ( M - 1 ) / N ) ) } ) )

  disjoint b v
  disjoint b z
  disjoint B b
  disjoint v z
  disjoint B v
  disjoint B z
  disjoint b j
  disjoint b k
  disjoint b m
  disjoint b s
  disjoint b u
  disjoint b x
  disjoint F b
  disjoint j k
  disjoint j m
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m x
  disjoint m z
  disjoint F m
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s z
  disjoint F s
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint F u
  disjoint v x
  disjoint F v
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint L z
  disjoint M b
  disjoint M j
  disjoint M k
  disjoint M m
  disjoint M s
  disjoint M u
  disjoint M v
  disjoint M x
  disjoint M z
  disjoint P b
  disjoint P k
  disjoint P m
  disjoint P u
  disjoint P v
  disjoint P x
  disjoint P z
  disjoint C b
  disjoint C j
  disjoint C k
  disjoint C s
  disjoint C u
  disjoint C v
  disjoint C z
  disjoint j ph
  disjoint ph s
  disjoint ph x
  disjoint ph z
  disjoint ps z
  disjoint N b
  disjoint N k
  disjoint N m
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N z
  disjoint S b
  disjoint S j
  disjoint S k
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S z
  disjoint X j
  disjoint G b
  disjoint G j
  disjoint G k
  disjoint G m
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint G x
  disjoint G z
  disjoint T b
  disjoint T j
  disjoint T k
  disjoint T m
  disjoint T s
  disjoint T u
  disjoint T v
  disjoint T x
  disjoint T z
  disjoint J b
  disjoint J j
  disjoint J k
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J z
  disjoint Q b
  disjoint Q k
  disjoint Q m
  disjoint Q u
  disjoint Q v
  disjoint Q x
  disjoint Q z
  disjoint W k
  disjoint W m
  disjoint W x
  disjoint W z
  disjoint b y
  disjoint v y
  disjoint y z
  disjoint B y
  disjoint a b
  disjoint a c
  disjoint a f
  disjoint a g
  disjoint a j
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b n
  disjoint b t
  disjoint b w
  disjoint c f
  disjoint c g
  disjoint c j
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint F c
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j n
  disjoint j t
  disjoint j w
  disjoint j y
  disjoint k n
  disjoint k t
  disjoint k w
  disjoint k y
  disjoint m n
  disjoint m t
  disjoint m w
  disjoint m y
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s t
  disjoint s w
  disjoint s y
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u w
  disjoint u y
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint F y
  disjoint L n
  disjoint L y
  disjoint K f
  disjoint K y
  disjoint M a
  disjoint M c
  disjoint M y
  disjoint P f
  disjoint P g
  disjoint P n
  disjoint C a
  disjoint C c
  disjoint C f
  disjoint C g
  disjoint C n
  disjoint C y
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint n ph
  disjoint ph y
  disjoint N c
  disjoint N n
  disjoint N y
  disjoint S a
  disjoint S f
  disjoint S g
  disjoint S n
  disjoint X a
  disjoint G a
  disjoint G f
  disjoint G g
  disjoint G n
  disjoint G t
  disjoint G w
  disjoint G y
  disjoint T a
  disjoint T c
  disjoint T y
  disjoint J a
  disjoint J c
  disjoint J f
  disjoint J g
  disjoint J n
  disjoint Q c
  disjoint Q n
  disjoint Q y
  assert |- ( ( ph /\ ps ) -> ( ( Q ` M ) : W --> B /\ ( F o. ( Q ` M ) ) = ( G |` W ) ) )

  proof
    wph
    wps
    wa
    #
    cW
    cB
    cM
    cQ
    cfv
    #
    wf
    #
    cF
    @1
    ccom
    #
    cG
    cW
    cres
    #
    wceq
    @0
    @2
    cW
    cB
    vz
    cW
    vz
    cv
    #
    cG
    cfv
    #
    cF
    cM
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    @7
    cQ
    cfv
    cfv
    #
    vb
    cv
    wcel
    vb
    cM
    cT
    cfv
    #
    c2nd
    cfv
    #
    crio
    #
    cres
    #
    ccnv
    #
    cfv
    #
    cmpt
    #
    wf
    @0
    vz
    cW
    @15
    cB
    @16
    wph
    wps
    @5
    cW
    wcel
    #
    @15
    cB
    wcel
    wph
    wps
    @17
    wa
    #
    wa
    #
    @12
    cB
    @15
    @19
    @12
    cC
    cuni
    #
    cB
    @19
    @12
    cC
    wcel
    @12
    @20
    wss
    @19
    @11
    cC
    @12
    @19
    @11
    @10
    c1st
    cfv
    #
    cS
    cfv
    wcel
    #
    @11
    cC
    wss
    wph
    @18
    vv
    vu
    cB
    cC
    cP
    cS
    cT
    vj
    vk
    cF
    cG
    cJ
    cL
    cM
    cN
    cX
    vs
    cvmliftlem.1
    cvmliftlem.b
    cvmliftlem.x
    cvmliftlem.f
    cvmliftlem.g
    cvmliftlem.p
    cvmliftlem.e
    cvmliftlem.n
    cvmliftlem.t
    cvmliftlem.a
    cvmliftlem.l
    wph
    wps
    cM
    c1
    cN
    cfz
    co
    wcel
    #
    @17
    cvmliftlem6.1
    adantrr
    #
    cvmliftlem1
    #
    vv
    vu
    cC
    cS
    @11
    @21
    vk
    cF
    cJ
    vs
    cvmliftlem.1
    cvmsss
    syl
    @19
    @12
    @11
    wcel
    #
    @9
    @12
    wcel
    #
    @19
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    @22
    @9
    cB
    wcel
    #
    @9
    cF
    cfv
    #
    @21
    wcel
    @26
    @27
    wa
    wph
    @28
    @18
    cvmliftlem.f
    adantr
    #
    @25
    @19
    @29
    @30
    @8
    cG
    cfv
    #
    wceq
    #
    @19
    @9
    cF
    ccnv
    @32
    csn
    cima
    wcel
    #
    @29
    @33
    wa
    #
    wph
    wps
    @34
    @17
    cvmliftlem6.2
    adantrr
    @19
    cB
    cX
    cF
    wf
    #
    cF
    cB
    wfn
    @34
    @35
    wb
    @19
    @28
    cF
    cC
    cJ
    ccn
    co
    wcel
    #
    @36
    @31
    cC
    cF
    cJ
    cvmcn
    #
    cF
    cC
    cJ
    cB
    cX
    cvmliftlem.b
    cvmliftlem.x
    cnf
    #
    3syl
    cB
    cX
    cF
    ffn
    cB
    @32
    @9
    cF
    fniniseg
    3syl
    mpbid
    #
    simpld
    @19
    @30
    @32
    @21
    @19
    @29
    @33
    @40
    simprd
    wph
    @18
    vv
    vu
    @8
    cB
    cC
    cP
    cS
    cT
    vj
    vk
    cF
    cG
    cJ
    cL
    cM
    cN
    cW
    cX
    vs
    cvmliftlem.1
    cvmliftlem.b
    cvmliftlem.x
    cvmliftlem.f
    cvmliftlem.g
    cvmliftlem.p
    cvmliftlem.e
    cvmliftlem.n
    cvmliftlem.t
    cvmliftlem.a
    cvmliftlem.l
    @24
    cvmliftlem5.3
    @19
    @8
    @8
    cM
    cN
    cdiv
    co
    #
    cicc
    co
    #
    cW
    @19
    @8
    cxr
    wcel
    @41
    cxr
    wcel
    @8
    @41
    cle
    wbr
    @8
    @42
    wcel
    @19
    @8
    @19
    @7
    cN
    @19
    cM
    cr
    wcel
    #
    @7
    cr
    wcel
    #
    @19
    cM
    @19
    @23
    cM
    cn
    wcel
    #
    @24
    cM
    cN
    elfznn
    #
    syl
    nnred
    #
    cM
    peano2rem
    syl
    #
    wph
    cN
    cn
    wcel
    @18
    cvmliftlem.n
    adantr
    #
    nndivred
    #
    rexrd
    @19
    @41
    @19
    cM
    cN
    @47
    @49
    nndivred
    #
    rexrd
    @19
    @8
    @41
    @50
    @51
    @19
    @7
    cM
    clt
    wbr
    #
    @8
    @41
    clt
    wbr
    #
    @19
    cM
    @47
    ltm1d
    @19
    @44
    @43
    cN
    cr
    wcel
    cc0
    cN
    clt
    wbr
    @52
    @53
    wb
    @48
    @47
    @19
    cN
    @49
    nnred
    @19
    cN
    @49
    nngt0d
    @7
    cM
    cN
    ltdiv1
    syl112anc
    mpbid
    ltled
    @8
    @41
    lbicc2
    syl3anc
    cvmliftlem5.3
    syl6eleqr
    cvmliftlem3
    eqeltrd
    vb
    vv
    vu
    @9
    cB
    cC
    cS
    @11
    @21
    vk
    cF
    cJ
    @12
    vs
    cvmliftlem.1
    cvmliftlem.b
    @12
    eqid
    cvmsiota
    syl13anc
    simpld
    #
    sseldd
    @12
    cC
    elssuni
    syl
    cvmliftlem.b
    syl6sseqr
    @19
    @21
    @12
    @6
    @14
    @19
    @12
    @21
    @13
    wf1o
    #
    @21
    @12
    @14
    wf1o
    @21
    @12
    @14
    wf
    @19
    @28
    @22
    @26
    @55
    @31
    @25
    @54
    vv
    vu
    @12
    cC
    cS
    @11
    @21
    vk
    cF
    cJ
    vs
    cvmliftlem.1
    cvmsf1o
    syl3anc
    #
    @12
    @21
    @13
    f1ocnv
    @21
    @12
    @14
    f1of
    3syl
    wph
    @18
    vv
    vu
    @5
    cB
    cC
    cP
    cS
    cT
    vj
    vk
    cF
    cG
    cJ
    cL
    cM
    cN
    cW
    cX
    vs
    cvmliftlem.1
    cvmliftlem.b
    cvmliftlem.x
    cvmliftlem.f
    cvmliftlem.g
    cvmliftlem.p
    cvmliftlem.e
    cvmliftlem.n
    cvmliftlem.t
    cvmliftlem.a
    cvmliftlem.l
    @24
    cvmliftlem5.3
    wph
    wps
    @17
    simprr
    #
    cvmliftlem3
    #
    ffvelrnd
    #
    sseldd
    anassrs
    #
    @16
    eqid
    fmptd
    @0
    cW
    cB
    @1
    @16
    wph
    wps
    @45
    @1
    @16
    wceq
    @0
    @23
    @45
    cvmliftlem6.1
    @46
    syl
    wph
    vx
    vz
    vv
    vu
    cB
    cC
    cP
    cQ
    cS
    cT
    vj
    vk
    vm
    cF
    cG
    cJ
    cL
    cM
    cN
    cW
    cX
    vs
    vb
    cvmliftlem.1
    cvmliftlem.b
    cvmliftlem.x
    cvmliftlem.f
    cvmliftlem.g
    cvmliftlem.p
    cvmliftlem.e
    cvmliftlem.n
    cvmliftlem.t
    cvmliftlem.a
    cvmliftlem.l
    cvmliftlem.q
    cvmliftlem5.3
    cvmliftlem5
    syldan
    #
    feq1d
    mpbird
    @0
    vz
    cW
    @15
    cF
    cfv
    #
    cmpt
    vz
    cW
    @5
    @4
    cfv
    #
    cmpt
    @3
    @4
    @0
    vz
    cW
    @62
    @63
    wph
    wps
    @17
    @62
    @63
    wceq
    @19
    @63
    @6
    @15
    @13
    cfv
    #
    @62
    @19
    @17
    @63
    @6
    wceq
    @57
    @5
    cW
    cG
    fvres
    syl
    @19
    @55
    @6
    @21
    wcel
    @64
    @6
    wceq
    @56
    @58
    @12
    @21
    @6
    @13
    f1ocnvfv2
    syl2anc
    @19
    @15
    @12
    wcel
    @64
    @62
    wceq
    @59
    @15
    @12
    cF
    fvres
    syl
    3eqtr2rd
    anassrs
    mpteq2dva
    @0
    vz
    vy
    cW
    cB
    @15
    vy
    cv
    #
    cF
    cfv
    @62
    @1
    cF
    @60
    @61
    @0
    vy
    cB
    cX
    cF
    wph
    @36
    wps
    wph
    @28
    @37
    @36
    cvmliftlem.f
    @38
    @39
    3syl
    adantr
    feqmptd
    @65
    @15
    cF
    fveq2
    fmptco
    @0
    vz
    cW
    cX
    @4
    @0
    cc0
    c1
    cicc
    co
    #
    cX
    cW
    cG
    wph
    @66
    cX
    cG
    wf
    #
    wps
    wph
    cG
    cii
    cJ
    ccn
    co
    wcel
    @67
    cvmliftlem.g
    cG
    cii
    cJ
    @66
    cX
    iiuni
    cvmliftlem.x
    cnf
    syl
    adantr
    wph
    wps
    vv
    vu
    cB
    cC
    cP
    cS
    cT
    vj
    vk
    cF
    cG
    cJ
    cL
    cM
    cN
    cW
    cX
    vs
    cvmliftlem.1
    cvmliftlem.b
    cvmliftlem.x
    cvmliftlem.f
    cvmliftlem.g
    cvmliftlem.p
    cvmliftlem.e
    cvmliftlem.n
    cvmliftlem.t
    cvmliftlem.a
    cvmliftlem.l
    cvmliftlem6.1
    cvmliftlem5.3
    cvmliftlem2
    fssresd
    feqmptd
    3eqtr4d
    jca
end
