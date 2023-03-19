include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cima.mm"
include "clt.mm"
include "cres.mm"
include "wiso.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cpw.mm"
include "wrex.mm"
include "ccnv.mm"
include "wo.mm"
include "cmin.mm"
include "wcel.mm"
include "wn.mm"
include "erdszelem10.mm"
include "cn.mm"
include "adantr.mm"
include "cr.mm"
include "wf1.mm"
include "ltso.mm"
include "simprl.mm"
include "simprr.mm"
include "erdszelem7.mm"
include "expr.mm"
include "gtso.mm"
include "orim12d.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "r19.43.mm"
include "sylibr.mm"

theorem erdszelem11
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let cS: class S
  let cT: class T
  let vn: setvar n
  let cF: class F
  let cI: class I
  let cJ: class J
  let cN: class N
  let vs: setvar s
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let vm: setvar m
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
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint I n
  disjoint I s
  disjoint I x
  disjoint I y
  disjoint J n
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint R s
  disjoint R x
  disjoint R y
  disjoint N n
  disjoint N s
  disjoint N x
  disjoint N y
  disjoint n ph
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T s
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
  disjoint m n
  disjoint m s
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n w
  disjoint n z
  disjoint s w
  disjoint s z
  disjoint F w
  disjoint F z
  disjoint K f
  disjoint K s
  disjoint K z
  disjoint A f
  disjoint A s
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint O f
  disjoint O s
  disjoint O w
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint R m
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
  disjoint N w
  disjoint N z
  disjoint a f
  disjoint a ph
  disjoint b f
  disjoint b ph
  disjoint f ph
  disjoint m ph
  disjoint ph w
  disjoint ph z
  disjoint S m
  disjoint T a
  disjoint T b
  disjoint T m
  disjoint T w
  disjoint T z
  assert |- ( ph -> E. s e. ~P ( 1 ... N ) ( ( R <_ ( # ` s ) /\ ( F |` s ) Isom < , < ( s , ( F " s ) ) ) \/ ( S <_ ( # ` s ) /\ ( F |` s ) Isom < , `' < ( s , ( F " s ) ) ) ) )

  proof
    wph
    cR
    vs
    cv
    #
    chash
    cfv
    #
    cle
    wbr
    @0
    cF
    @0
    cima
    #
    clt
    clt
    cF
    @0
    cres
    #
    wiso
    wa
    #
    vs
    c1
    cN
    cfz
    co
    #
    cpw
    #
    wrex
    #
    cS
    @1
    cle
    wbr
    @0
    @2
    clt
    clt
    ccnv
    #
    @3
    wiso
    wa
    #
    vs
    @6
    wrex
    #
    wo
    #
    @4
    @9
    wo
    vs
    @6
    wrex
    wph
    vm
    cv
    #
    cI
    cfv
    c1
    cR
    c1
    cmin
    co
    cfz
    co
    wcel
    wn
    #
    @12
    cJ
    cfv
    c1
    cS
    c1
    cmin
    co
    cfz
    co
    wcel
    wn
    #
    wo
    #
    vm
    @5
    wrex
    @11
    wph
    vx
    vy
    cR
    cS
    cT
    vm
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
    erdszelem.r
    erdszelem.s
    erdszelem.m
    erdszelem10
    wph
    @15
    @11
    vm
    @5
    wph
    @12
    @5
    wcel
    #
    wa
    @13
    @7
    @14
    @10
    wph
    @16
    @13
    @7
    wph
    @16
    @13
    wa
    #
    wa
    vx
    vy
    @12
    cR
    cF
    cI
    cN
    clt
    vs
    wph
    cN
    cn
    wcel
    #
    @17
    erdsze.n
    adantr
    wph
    @5
    cr
    cF
    wf1
    #
    @17
    erdsze.f
    adantr
    erdszelem.i
    ltso
    wph
    @16
    @13
    simprl
    wph
    cR
    cn
    wcel
    @17
    erdszelem.r
    adantr
    wph
    @16
    @13
    simprr
    erdszelem7
    expr
    wph
    @16
    @14
    @10
    wph
    @16
    @14
    wa
    #
    wa
    vx
    vy
    @12
    cS
    cF
    cJ
    cN
    @8
    vs
    wph
    @18
    @20
    erdsze.n
    adantr
    wph
    @19
    @20
    erdsze.f
    adantr
    erdszelem.j
    gtso
    wph
    @16
    @14
    simprl
    wph
    cS
    cn
    wcel
    @20
    erdszelem.s
    adantr
    wph
    @16
    @14
    simprr
    erdszelem7
    expr
    orim12d
    rexlimdva
    mpd
    @4
    @9
    vs
    @6
    r19.43
    sylibr
end
