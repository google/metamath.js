include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "chash.mm"
include "cv.mm"
include "cima.mm"
include "clt.mm"
include "cres.mm"
include "wiso.mm"
include "cpw.mm"
include "crab.mm"
include "cr.mm"
include "csup.mm"
include "wceq.mm"
include "erdszelem3.mm"
include "adantl.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "cin.mm"
include "csn.mm"
include "cvv.mm"
include "snex.mm"
include "cn0.mm"
include "cpnf.mm"
include "cun.mm"
include "hashf.mm"
include "fdmi.mm"
include "eleqtrri.mm"
include "erdszelem4.mm"
include "inelcm.mm"
include "sylancr.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "cfn.mm"
include "wss.mm"
include "cn.mm"
include "eqid.mm"
include "erdszelem2.mm"
include "simpli.mm"
include "simpri.mm"
include "nnssre.mm"
include "sstri.mm"
include "wor.mm"
include "w3a.mm"
include "ltso.mm"
include "fisupcl.mm"
include "mpan.mm"
include "mp3an13.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem erdszelem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let cK: class K
  let cN: class N
  let cO: class O
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let cI: class I
  let cJ: class J
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let cS: class S
  let cT: class T
  assume erdsze.n: |- ( ph -> N e. NN )
  assume erdsze.f: |- ( ph -> F : ( 1 ... N ) -1-1-> RR )
  assume erdszelem.k: |- K = ( x e. ( 1 ... N ) |-> sup ( ( # " { y e. ~P ( 1 ... x ) | ( ( F |` y ) Isom < , O ( y , ( F " y ) ) /\ x e. y ) } ) , RR , < ) )
  assume erdszelem.o: |- O Or RR

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint A x
  disjoint A y
  disjoint O x
  disjoint O y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
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
  disjoint F s
  disjoint F w
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
  disjoint A z
  disjoint J n
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint O f
  disjoint O s
  disjoint O w
  disjoint O z
  disjoint R m
  disjoint R s
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
  disjoint N s
  disjoint N w
  disjoint N z
  disjoint a f
  disjoint a ph
  disjoint b f
  disjoint b ph
  disjoint f ph
  disjoint m ph
  disjoint n ph
  disjoint ph s
  disjoint ph w
  disjoint ph z
  disjoint S m
  disjoint S s
  disjoint S x
  disjoint S y
  disjoint T a
  disjoint T b
  disjoint T m
  disjoint T s
  disjoint T w
  disjoint T z
  assert |- ( ( ph /\ A e. ( 1 ... N ) ) -> ( K ` A ) e. ( # " { y e. ~P ( 1 ... A ) | ( ( F |` y ) Isom < , O ( y , ( F " y ) ) /\ A e. y ) } ) )

  proof
    wph
    cA
    c1
    cN
    cfz
    co
    wcel
    #
    wa
    #
    cA
    cK
    cfv
    #
    chash
    vy
    cv
    #
    cF
    @3
    cima
    clt
    cO
    cF
    @3
    cres
    wiso
    cA
    @3
    wcel
    wa
    vy
    c1
    cA
    cfz
    co
    cpw
    crab
    #
    cima
    #
    cr
    clt
    csup
    #
    @5
    @0
    @2
    @6
    wceq
    wph
    wph
    vx
    vy
    cA
    cF
    cK
    cN
    cO
    erdsze.n
    erdsze.f
    erdszelem.k
    erdszelem3
    adantl
    @1
    @5
    c0
    wne
    #
    @6
    @5
    wcel
    #
    @1
    chash
    cdm
    #
    @4
    cin
    #
    c0
    wne
    #
    @7
    @1
    cA
    csn
    #
    @9
    wcel
    @12
    @4
    wcel
    @11
    @12
    cvv
    @9
    cA
    snex
    cvv
    cn0
    cpnf
    csn
    cun
    chash
    hashf
    fdmi
    eleqtrri
    wph
    vx
    vy
    cA
    cF
    cK
    cN
    cO
    erdsze.n
    erdsze.f
    erdszelem.k
    erdszelem.o
    erdszelem4
    @12
    @9
    @4
    inelcm
    sylancr
    @5
    c0
    @10
    c0
    chash
    @4
    imadisj
    necon3bii
    sylibr
    @5
    cfn
    wcel
    #
    @7
    @5
    cr
    wss
    #
    @8
    @13
    @5
    cn
    wss
    #
    vy
    cA
    @4
    cF
    cO
    @4
    eqid
    erdszelem2
    #
    simpli
    @5
    cn
    cr
    @13
    @15
    @16
    simpri
    nnssre
    sstri
    cr
    clt
    wor
    @13
    @7
    @14
    w3a
    @8
    ltso
    cr
    @5
    clt
    fisupcl
    mpan
    mp3an13
    syl
    eqeltrd
end
