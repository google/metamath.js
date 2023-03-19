include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "chash.mm"
include "cima.mm"
include "clt.mm"
include "cres.mm"
include "wiso.mm"
include "wel.mm"
include "wa.mm"
include "cpw.mm"
include "crab.mm"
include "cr.mm"
include "csup.mm"
include "cmpt.mm"
include "cfv.mm"
include "ccnv.mm"
include "cop.mm"
include "weq.mm"
include "wceq.mm"
include "wb.mm"
include "reseq2.mm"
include "isoeq1.mm"
include "syl.mm"
include "isoeq4.mm"
include "imaeq2.mm"
include "isoeq5.mm"
include "3bitrd.mm"
include "elequ2.mm"
include "anbi12d.mm"
include "cbvrabv.mm"
include "oveq2.mm"
include "pweqd.mm"
include "elequ1.mm"
include "anbi2d.mm"
include "rabeqbidv.mm"
include "syl5eq.mm"
include "imaeq2d.mm"
include "supeq1d.mm"
include "cbvmptv.mm"
include "eqid.mm"
include "erdszelem11.mm"

theorem erdsze
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cF: class F
  let cN: class N
  let vs: setvar s
  let vf: setvar f
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let cI: class I
  let cK: class K
  let cA: class A
  let cJ: class J
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let cT: class T
  assume erdsze.n: |- ( ph -> N e. NN )
  assume erdsze.f: |- ( ph -> F : ( 1 ... N ) -1-1-> RR )
  assume erdsze.r: |- ( ph -> R e. NN )
  assume erdsze.s: |- ( ph -> S e. NN )
  assume erdsze.l: |- ( ph -> ( ( R - 1 ) x. ( S - 1 ) ) < N )

  disjoint F s
  disjoint R s
  disjoint N s
  disjoint ph s
  disjoint S s
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
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
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint F f
  disjoint m n
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n s
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint I n
  disjoint I s
  disjoint I x
  disjoint I y
  disjoint K f
  disjoint K s
  disjoint K z
  disjoint A f
  disjoint A s
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint J n
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint O f
  disjoint O s
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint R m
  disjoint R x
  disjoint R y
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a s
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint N a
  disjoint b m
  disjoint b n
  disjoint b s
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint N b
  disjoint N m
  disjoint N n
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint a f
  disjoint a ph
  disjoint b f
  disjoint b ph
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S m
  disjoint S x
  disjoint S y
  disjoint T a
  disjoint T b
  disjoint T m
  disjoint T s
  disjoint T w
  disjoint T z
  assert |- ( ph -> E. s e. ~P ( 1 ... N ) ( ( R <_ ( # ` s ) /\ ( F |` s ) Isom < , < ( s , ( F " s ) ) ) \/ ( S <_ ( # ` s ) /\ ( F |` s ) Isom < , `' < ( s , ( F " s ) ) ) ) )

  proof
    wph
    vx
    vy
    cR
    cS
    vn
    c1
    cN
    cfz
    co
    #
    vn
    cv
    #
    vz
    @0
    chash
    vw
    cv
    #
    cF
    @2
    cima
    #
    clt
    clt
    cF
    @2
    cres
    #
    wiso
    #
    vz
    vw
    wel
    #
    wa
    #
    vw
    c1
    vz
    cv
    #
    cfz
    co
    #
    cpw
    #
    crab
    #
    cima
    #
    cr
    clt
    csup
    #
    cmpt
    #
    cfv
    @1
    vz
    @0
    chash
    @2
    @3
    clt
    clt
    ccnv
    #
    @4
    wiso
    #
    @6
    wa
    #
    vw
    @10
    crab
    #
    cima
    #
    cr
    clt
    csup
    #
    cmpt
    #
    cfv
    cop
    cmpt
    #
    vn
    cF
    @14
    @21
    cN
    vs
    erdsze.n
    erdsze.f
    vz
    vx
    @0
    @13
    chash
    vy
    cv
    #
    cF
    @23
    cima
    #
    clt
    clt
    cF
    @23
    cres
    #
    wiso
    #
    vx
    vy
    wel
    #
    wa
    #
    vy
    c1
    vx
    cv
    #
    cfz
    co
    #
    cpw
    #
    crab
    #
    cima
    #
    cr
    clt
    csup
    vz
    vx
    weq
    #
    cr
    @12
    @33
    clt
    @34
    @11
    @32
    chash
    @34
    @11
    @26
    vz
    vy
    wel
    #
    wa
    #
    vy
    @10
    crab
    @32
    @7
    @36
    vw
    vy
    @10
    vw
    vy
    weq
    #
    @5
    @26
    @6
    @35
    @37
    @5
    @2
    @3
    clt
    clt
    @25
    wiso
    #
    @23
    @3
    clt
    clt
    @25
    wiso
    #
    @26
    @37
    @4
    @25
    wceq
    #
    @5
    @38
    wb
    @2
    @23
    cF
    reseq2
    #
    @2
    @3
    clt
    clt
    @25
    @4
    isoeq1
    syl
    @2
    @3
    @23
    clt
    clt
    @25
    isoeq4
    @37
    @3
    @24
    wceq
    #
    @39
    @26
    wb
    @2
    @23
    cF
    imaeq2
    #
    @23
    @3
    @24
    clt
    clt
    @25
    isoeq5
    syl
    3bitrd
    vw
    vy
    vz
    elequ2
    #
    anbi12d
    cbvrabv
    @34
    @36
    @28
    vy
    @10
    @31
    @34
    @9
    @30
    @8
    @29
    c1
    cfz
    oveq2
    pweqd
    #
    @34
    @35
    @27
    @26
    vz
    vx
    vy
    elequ1
    #
    anbi2d
    rabeqbidv
    syl5eq
    imaeq2d
    supeq1d
    cbvmptv
    vz
    vx
    @0
    @20
    chash
    @23
    @24
    clt
    @15
    @25
    wiso
    #
    @27
    wa
    #
    vy
    @31
    crab
    #
    cima
    #
    cr
    clt
    csup
    @34
    cr
    @19
    @50
    clt
    @34
    @18
    @49
    chash
    @34
    @18
    @47
    @35
    wa
    #
    vy
    @10
    crab
    @49
    @17
    @51
    vw
    vy
    @10
    @37
    @16
    @47
    @6
    @35
    @37
    @16
    @2
    @3
    clt
    @15
    @25
    wiso
    #
    @23
    @3
    clt
    @15
    @25
    wiso
    #
    @47
    @37
    @40
    @16
    @52
    wb
    @41
    @2
    @3
    clt
    @15
    @25
    @4
    isoeq1
    syl
    @2
    @3
    @23
    clt
    @15
    @25
    isoeq4
    @37
    @42
    @53
    @47
    wb
    @43
    @23
    @3
    @24
    clt
    @15
    @25
    isoeq5
    syl
    3bitrd
    @44
    anbi12d
    cbvrabv
    @34
    @51
    @48
    vy
    @10
    @31
    @45
    @34
    @35
    @27
    @47
    @46
    anbi2d
    rabeqbidv
    syl5eq
    imaeq2d
    supeq1d
    cbvmptv
    @22
    eqid
    erdsze.r
    erdsze.s
    erdsze.l
    erdszelem11
end
