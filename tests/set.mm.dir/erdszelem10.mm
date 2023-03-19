include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cxp.mm"
include "wcel.mm"
include "wn.mm"
include "wrex.mm"
include "wo.mm"
include "crn.mm"
include "wss.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "cfn.mm"
include "wi.mm"
include "fzfi.mm"
include "xpfi.mm"
include "mp2an.mm"
include "ssdomg.mm"
include "ax-mp.mm"
include "domnsym.mm"
include "syl.mm"
include "cen.mm"
include "chash.mm"
include "clt.mm"
include "cmul.mm"
include "wceq.mm"
include "hashxp.mm"
include "cn.mm"
include "cn0.mm"
include "nnm1nn0.mm"
include "hashfz1.mm"
include "3syl.mm"
include "oveq12d.mm"
include "syl5eq.mm"
include "nnnn0d.mm"
include "3brtr4d.mm"
include "wb.mm"
include "fzfid.mm"
include "hashsdom.mm"
include "sylancr.mm"
include "mpbid.mm"
include "wf1.mm"
include "wf1o.mm"
include "erdszelem9.mm"
include "f1f1orn.mm"
include "ovex.mm"
include "f1oen.mm"
include "sdomentr.mm"
include "syl2anc.mm"
include "nsyl3.mm"
include "wa.mm"
include "wex.mm"
include "nss.mm"
include "df-rex.mm"
include "bitr4i.mm"
include "sylib.mm"
include "wfn.mm"
include "f1fn.mm"
include "eleq1.mm"
include "notbid.mm"
include "rexrn.mm"
include "cop.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "eleq1d.mm"
include "opelxp.mm"
include "syl6bb.mm"
include "ianor.mm"
include "rexbidva.mm"

theorem erdszelem10
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cT: class T
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cI: class I
  let cJ: class J
  let cN: class N
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let vs: setvar s
  let cK: class K
  let cA: class A
  let cO: class O
  let va: setvar a
  let vb: setvar b
  assume erdsze.n: |- ( ph -> N e. NN )
  assume erdsze.f: |- ( ph -> F : ( 1 ... N ) -1-1-> RR )
  assume erdszelem.i: |- I = ( x e. ( 1 ... N ) |-> sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y ) Isom < , < ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) )
  assume erdszelem.j: |- J = ( x e. ( 1 ... N ) |-> sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y ) Isom < , `' < ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) )
  assume erdszelem.t: |- T = ( n e. ( 1 ... N ) |-> <. ( I ` n ) , ( J ` n ) >. )
  assume erdszelem.r: |- ( ph -> R e. NN )
  assume erdszelem.s: |- ( ph -> S e. NN )
  assume erdszelem.m: |- ( ph -> ( ( R - 1 ) x. ( S - 1 ) ) < N )

  disjoint x y
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint F m
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint I n
  disjoint I x
  disjoint I y
  disjoint J n
  disjoint J x
  disjoint J y
  disjoint R m
  disjoint R x
  disjoint R y
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint S m
  disjoint S x
  disjoint S y
  disjoint T m
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint f m
  disjoint f n
  disjoint f s
  disjoint F f
  disjoint m s
  disjoint m w
  disjoint m z
  disjoint n s
  disjoint n w
  disjoint n z
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint F w
  disjoint F z
  disjoint I s
  disjoint K f
  disjoint K s
  disjoint K z
  disjoint A f
  disjoint A s
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint J s
  disjoint O f
  disjoint O s
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint R s
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
  disjoint N s
  disjoint N w
  disjoint N z
  disjoint a f
  disjoint a ph
  disjoint b f
  disjoint b ph
  disjoint f ph
  disjoint ph s
  disjoint ph w
  disjoint ph z
  disjoint S s
  disjoint T a
  disjoint T b
  disjoint T s
  disjoint T w
  disjoint T z
  assert |- ( ph -> E. m e. ( 1 ... N ) ( -. ( I ` m ) e. ( 1 ... ( R - 1 ) ) \/ -. ( J ` m ) e. ( 1 ... ( S - 1 ) ) ) )

  proof
    wph
    vm
    cv
    #
    cT
    cfv
    #
    c1
    cR
    c1
    cmin
    co
    #
    cfz
    co
    #
    c1
    cS
    c1
    cmin
    co
    #
    cfz
    co
    #
    cxp
    #
    wcel
    #
    wn
    #
    vm
    c1
    cN
    cfz
    co
    #
    wrex
    #
    @0
    cI
    cfv
    #
    @3
    wcel
    #
    wn
    @0
    cJ
    cfv
    #
    @5
    wcel
    #
    wn
    wo
    #
    vm
    @9
    wrex
    wph
    vs
    cv
    #
    @6
    wcel
    #
    wn
    #
    vs
    cT
    crn
    #
    wrex
    #
    @10
    wph
    @19
    @6
    wss
    #
    wn
    #
    @20
    @21
    @6
    @19
    csdm
    wbr
    #
    wph
    @21
    @19
    @6
    cdom
    wbr
    #
    @23
    wn
    @6
    cfn
    wcel
    #
    @21
    @24
    wi
    @3
    cfn
    wcel
    #
    @5
    cfn
    wcel
    #
    @25
    c1
    @2
    fzfi
    #
    c1
    @4
    fzfi
    #
    @3
    @5
    xpfi
    mp2an
    #
    @19
    @6
    cfn
    ssdomg
    ax-mp
    @19
    @6
    domnsym
    syl
    wph
    @6
    @9
    csdm
    wbr
    #
    @9
    @19
    cen
    wbr
    #
    @23
    wph
    @6
    chash
    cfv
    #
    @9
    chash
    cfv
    #
    clt
    wbr
    #
    @31
    wph
    @2
    @4
    cmul
    co
    #
    cN
    @33
    @34
    clt
    erdszelem.m
    wph
    @33
    @3
    chash
    cfv
    #
    @5
    chash
    cfv
    #
    cmul
    co
    #
    @36
    @26
    @27
    @33
    @39
    wceq
    @28
    @29
    @3
    @5
    hashxp
    mp2an
    wph
    @37
    @2
    @38
    @4
    cmul
    wph
    cR
    cn
    wcel
    @2
    cn0
    wcel
    @37
    @2
    wceq
    erdszelem.r
    cR
    nnm1nn0
    @2
    hashfz1
    3syl
    wph
    cS
    cn
    wcel
    @4
    cn0
    wcel
    @38
    @4
    wceq
    erdszelem.s
    cS
    nnm1nn0
    @4
    hashfz1
    3syl
    oveq12d
    syl5eq
    wph
    cN
    cn0
    wcel
    @34
    cN
    wceq
    wph
    cN
    erdsze.n
    nnnn0d
    cN
    hashfz1
    syl
    3brtr4d
    wph
    @25
    @9
    cfn
    wcel
    @35
    @31
    wb
    @30
    wph
    c1
    cN
    fzfid
    @6
    @9
    hashsdom
    sylancr
    mpbid
    wph
    @9
    cn
    cn
    cxp
    #
    cT
    wf1
    #
    @9
    @19
    cT
    wf1o
    @32
    wph
    vx
    vy
    cT
    vn
    cF
    cI
    cJ
    cN
    erdsze.n
    erdsze.f
    erdszelem.i
    erdszelem.j
    erdszelem.t
    erdszelem9
    #
    @9
    @40
    cT
    f1f1orn
    @9
    @19
    cT
    c1
    cN
    cfz
    ovex
    f1oen
    3syl
    @6
    @9
    @19
    sdomentr
    syl2anc
    nsyl3
    @22
    @16
    @19
    wcel
    @18
    wa
    vs
    wex
    @20
    vs
    @19
    @6
    nss
    @18
    vs
    @19
    df-rex
    bitr4i
    sylib
    wph
    @41
    cT
    @9
    wfn
    @20
    @10
    wb
    @42
    @9
    @40
    cT
    f1fn
    @18
    @8
    vs
    vm
    @9
    cT
    @16
    @1
    wceq
    @17
    @7
    @16
    @1
    @6
    eleq1
    notbid
    rexrn
    3syl
    mpbid
    wph
    @8
    @15
    vm
    @9
    wph
    @0
    @9
    wcel
    #
    wa
    #
    @8
    @12
    @14
    wa
    #
    wn
    @15
    @44
    @7
    @45
    @44
    @7
    @11
    @13
    cop
    #
    @6
    wcel
    @45
    @44
    @1
    @46
    @6
    @43
    @1
    @46
    wceq
    wph
    vn
    @0
    vn
    cv
    #
    cI
    cfv
    #
    @47
    cJ
    cfv
    #
    cop
    @46
    @9
    cT
    @47
    @0
    wceq
    @48
    @11
    @49
    @13
    @47
    @0
    cI
    fveq2
    @47
    @0
    cJ
    fveq2
    opeq12d
    erdszelem.t
    @11
    @13
    opex
    fvmpt
    adantl
    eleq1d
    @11
    @13
    @3
    @5
    opelxp
    syl6bb
    notbid
    @12
    @14
    ianor
    syl6bb
    rexbidva
    mpbid
end
