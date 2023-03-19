include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "cmin.mm"
include "cdiv.mm"
include "c2nd.mm"
include "crio.mm"
include "cres.mm"
include "ccnv.mm"
include "cmpt.mm"
include "crest.mm"
include "ccn.mm"
include "cn.mm"
include "wceq.mm"
include "elfznn.mm"
include "cvmliftlem5.mm"
include "sylan2.mm"
include "ccvm.mm"
include "ctop.mm"
include "wss.mm"
include "adantr.mm"
include "cvmtop1.mm"
include "cnrest2r.mm"
include "3syl.mm"
include "c1st.mm"
include "cr.mm"
include "ctopon.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "retopon.mm"
include "eqeltri.mm"
include "cc0.mm"
include "cicc.mm"
include "simpr.mm"
include "cvmliftlem2.mm"
include "unitssre.mm"
include "syl6ss.mm"
include "resttopon.mm"
include "sylancr.mm"
include "cii.mm"
include "eqid.mm"
include "iitopon.mm"
include "a1i.mm"
include "wf.mm"
include "iiuni.mm"
include "cnf.mm"
include "syl.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "cnmpt1res.mm"
include "dfii2.mm"
include "oveq1i.mm"
include "eqtr4i.mm"
include "cvv.mm"
include "retop.mm"
include "ovexd.mm"
include "restabs.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "eleqtrd.mm"
include "wb.mm"
include "cvmtop2.mm"
include "toptopon.mm"
include "sylib.mm"
include "simprl.mm"
include "simprr.mm"
include "cvmliftlem3.mm"
include "anassrs.mm"
include "fmptd.mm"
include "frn.mm"
include "cuni.mm"
include "cvmliftlem1.mm"
include "cvmsrcl.mm"
include "elssuni.mm"
include "syl6sseqr.mm"
include "cnrest2.mm"
include "mpbid.mm"
include "chmeo.mm"
include "csn.mm"
include "cima.mm"
include "cvmliftlem7.mm"
include "wfn.mm"
include "cvmcn.mm"
include "ffn.mm"
include "fniniseg.mm"
include "simpld.mm"
include "simprd.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "adantl.mm"
include "nnred.mm"
include "peano2rem.mm"
include "nndivred.mm"
include "rexrd.mm"
include "clt.mm"
include "ltm1d.mm"
include "nngt0d.mm"
include "ltdiv1.mm"
include "syl112anc.mm"
include "ltled.mm"
include "lbicc2.mm"
include "syl6eleqr.mm"
include "eqeltrd.mm"
include "cvmsiota.mm"
include "syl13anc.mm"
include "cvmshmeo.mm"
include "syl2anc.mm"
include "hmeocnvcn.mm"
include "cnmpt11f.mm"
include "sseldd.mm"

theorem cvmliftlem8
  let wph: wff ph
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
  let wps: wff ps
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
  disjoint ps z
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
  assert |- ( ( ph /\ M e. ( 1 ... N ) ) -> ( Q ` M ) e. ( ( L |`t W ) Cn C ) )

  proof
    wph
    cM
    c1
    cN
    cfz
    co
    wcel
    #
    wa
    #
    cM
    cQ
    cfv
    #
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
    @5
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
    cmpt
    #
    cL
    cW
    crest
    co
    #
    cC
    ccn
    co
    #
    @0
    wph
    cM
    cn
    wcel
    #
    @2
    @13
    wceq
    cM
    cN
    elfznn
    #
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
    sylan2
    @1
    @14
    cC
    @10
    crest
    co
    #
    ccn
    co
    #
    @15
    @13
    @1
    cF
    cC
    cJ
    ccvm
    co
    wcel
    #
    cC
    ctop
    wcel
    @19
    @15
    wss
    wph
    @20
    @0
    cvmliftlem.f
    adantr
    #
    cC
    cF
    cJ
    cvmtop1
    @10
    @14
    cC
    cnrest2r
    3syl
    @1
    vz
    @4
    @12
    @14
    cJ
    @8
    c1st
    cfv
    #
    crest
    co
    #
    @18
    cW
    @1
    cL
    cr
    ctopon
    cfv
    #
    wcel
    cW
    cr
    wss
    @14
    cW
    ctopon
    cfv
    wcel
    cL
    cioo
    crn
    ctg
    cfv
    #
    @24
    cvmliftlem.l
    retopon
    eqeltri
    @1
    cW
    cc0
    c1
    cicc
    co
    #
    cr
    wph
    @0
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
    wph
    @0
    simpr
    #
    cvmliftlem5.3
    cvmliftlem2
    #
    unitssre
    syl6ss
    cW
    cL
    cr
    resttopon
    sylancr
    @1
    vz
    cW
    @4
    cmpt
    #
    @14
    cJ
    ccn
    co
    #
    wcel
    #
    @29
    @14
    @23
    ccn
    co
    wcel
    #
    @1
    @29
    cii
    cW
    crest
    co
    #
    cJ
    ccn
    co
    @30
    @1
    vz
    @4
    cii
    @33
    cJ
    @26
    cW
    @33
    eqid
    cii
    @26
    ctopon
    cfv
    wcel
    @1
    iitopon
    a1i
    @28
    @1
    cG
    vz
    @26
    @4
    cmpt
    cii
    cJ
    ccn
    co
    #
    @1
    vz
    @26
    cX
    cG
    @1
    cG
    @34
    wcel
    #
    @26
    cX
    cG
    wf
    wph
    @35
    @0
    cvmliftlem.g
    adantr
    #
    cG
    cii
    cJ
    @26
    cX
    iiuni
    cvmliftlem.x
    cnf
    syl
    feqmptd
    @36
    eqeltrrd
    cnmpt1res
    @1
    @33
    @14
    cJ
    ccn
    @1
    @33
    cL
    @26
    crest
    co
    #
    cW
    crest
    co
    #
    @14
    cii
    @37
    cW
    crest
    cii
    @25
    @26
    crest
    co
    @37
    dfii2
    cL
    @25
    @26
    crest
    cvmliftlem.l
    oveq1i
    eqtr4i
    oveq1i
    @1
    cL
    ctop
    wcel
    #
    cW
    @26
    wss
    @26
    cvv
    wcel
    @38
    @14
    wceq
    @39
    @1
    cL
    @25
    ctop
    cvmliftlem.l
    retop
    eqeltri
    a1i
    @28
    @1
    cc0
    c1
    cicc
    ovexd
    cW
    @26
    cL
    ctop
    cvv
    restabs
    syl3anc
    syl5eq
    oveq1d
    eleqtrd
    @1
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @29
    crn
    @22
    wss
    #
    @22
    cX
    wss
    @31
    @32
    wb
    @1
    cJ
    ctop
    wcel
    #
    @40
    @1
    @20
    @42
    @21
    cC
    cF
    cJ
    cvmtop2
    syl
    cJ
    cX
    cvmliftlem.x
    toptopon
    sylib
    @1
    cW
    @22
    @29
    wf
    @41
    @1
    vz
    cW
    @4
    @22
    @29
    wph
    @0
    @3
    cW
    wcel
    #
    @4
    @22
    wcel
    wph
    @0
    @43
    wa
    vv
    vu
    @3
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
    wph
    @0
    @43
    simprl
    cvmliftlem5.3
    wph
    @0
    @43
    simprr
    cvmliftlem3
    anassrs
    @29
    eqid
    fmptd
    cW
    @22
    @29
    frn
    syl
    @1
    @22
    cJ
    cuni
    #
    cX
    @1
    @9
    @22
    cS
    cfv
    wcel
    #
    @22
    cJ
    wcel
    @22
    @44
    wss
    wph
    @0
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
    @27
    cvmliftlem1
    #
    vv
    vu
    cC
    cS
    @9
    @22
    vk
    cF
    cJ
    vs
    cvmliftlem.1
    cvmsrcl
    @22
    cJ
    elssuni
    3syl
    cvmliftlem.x
    syl6sseqr
    @22
    @29
    @14
    cJ
    cX
    cnrest2
    syl3anc
    mpbid
    @1
    @11
    @18
    @23
    chmeo
    co
    wcel
    #
    @12
    @23
    @18
    ccn
    co
    wcel
    @1
    @45
    @10
    @9
    wcel
    #
    @47
    @46
    @1
    @48
    @7
    @10
    wcel
    #
    @1
    @20
    @45
    @7
    cB
    wcel
    #
    @7
    cF
    cfv
    #
    @22
    wcel
    @48
    @49
    wa
    @21
    @46
    @1
    @50
    @51
    @6
    cG
    cfv
    #
    wceq
    #
    @1
    @7
    cF
    ccnv
    @52
    csn
    cima
    wcel
    #
    @50
    @53
    wa
    #
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
    cvmliftlem7
    @1
    cB
    cX
    cF
    wf
    #
    cF
    cB
    wfn
    @54
    @55
    wb
    @1
    @20
    cF
    cC
    cJ
    ccn
    co
    wcel
    @56
    @21
    cC
    cF
    cJ
    cvmcn
    cF
    cC
    cJ
    cB
    cX
    cvmliftlem.b
    cvmliftlem.x
    cnf
    3syl
    cB
    cX
    cF
    ffn
    cB
    @52
    @7
    cF
    fniniseg
    3syl
    mpbid
    #
    simpld
    @1
    @51
    @52
    @22
    @1
    @50
    @53
    @57
    simprd
    wph
    @0
    vv
    vu
    @6
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
    @27
    cvmliftlem5.3
    @1
    @6
    @6
    cM
    cN
    cdiv
    co
    #
    cicc
    co
    #
    cW
    @1
    @6
    cxr
    wcel
    @58
    cxr
    wcel
    @6
    @58
    cle
    wbr
    @6
    @59
    wcel
    @1
    @6
    @1
    @5
    cN
    @1
    cM
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @1
    cM
    @0
    @16
    wph
    @17
    adantl
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
    @0
    cvmliftlem.n
    adantr
    #
    nndivred
    #
    rexrd
    @1
    @58
    @1
    cM
    cN
    @62
    @64
    nndivred
    #
    rexrd
    @1
    @6
    @58
    @65
    @66
    @1
    @5
    cM
    clt
    wbr
    #
    @6
    @58
    clt
    wbr
    #
    @1
    cM
    @62
    ltm1d
    @1
    @61
    @60
    cN
    cr
    wcel
    cc0
    cN
    clt
    wbr
    @67
    @68
    wb
    @63
    @62
    @1
    cN
    @64
    nnred
    @1
    cN
    @64
    nngt0d
    @5
    cM
    cN
    ltdiv1
    syl112anc
    mpbid
    ltled
    @6
    @58
    lbicc2
    syl3anc
    cvmliftlem5.3
    syl6eleqr
    cvmliftlem3
    eqeltrd
    vb
    vv
    vu
    @7
    cB
    cC
    cS
    @9
    @22
    vk
    cF
    cJ
    @10
    vs
    cvmliftlem.1
    cvmliftlem.b
    @10
    eqid
    cvmsiota
    syl13anc
    simpld
    vv
    vu
    @10
    cC
    cS
    @9
    @22
    vk
    cF
    cJ
    vs
    cvmliftlem.1
    cvmshmeo
    syl2anc
    @11
    @18
    @23
    hmeocnvcn
    syl
    cnmpt11f
    sseldd
    eqeltrd
end
