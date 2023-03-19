include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "wf1o.mm"
include "cfv.mm"
include "wceq.mm"
include "cpr.mm"
include "cun.mm"
include "cop.mm"
include "cin.mm"
include "c0.mm"
include "cz.mm"
include "wcel.mm"
include "cvv.mm"
include "1z.mm"
include "f1oprswap.mm"
include "mp2an.mm"
include "a1i.mm"
include "chash.mm"
include "cmin.mm"
include "subfacp1lem1.mm"
include "simp1d.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "wb.mm"
include "simp2d.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "f1oeq2.mm"
include "syl5bbr.mm"
include "f1oeq3.mm"
include "bitrd.mm"
include "syl.mm"
include "mpbid.mm"
include "csn.mm"
include "wfun.mm"
include "f1ofun.mm"
include "wss.mm"
include "cdm.mm"
include "snsspr1.mm"
include "ssun2.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "1ex.mm"
include "snid.mm"
include "dmsnop.mm"
include "eleqtrri.mm"
include "funssfv.mm"
include "mp3an23.mm"
include "fvsn.mm"
include "syl6eq.mm"
include "snsspr2.mm"
include "3jca.mm"

theorem subfacp1lem2a
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cK: class K
  let cM: class M
  let cN: class N
  let vg: setvar g
  let vh: setvar h
  let vm: setvar m
  let vs: setvar s
  let vz: setvar z
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let cB: class B
  let cC: class C
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )
  assume subfac.n: |- S = ( n e. NN0 |-> ( D ` ( 1 ... n ) ) )
  assume subfacp1lem.a: |- A = { f | ( f : ( 1 ... ( N + 1 ) ) -1-1-onto-> ( 1 ... ( N + 1 ) ) /\ A. y e. ( 1 ... ( N + 1 ) ) ( f ` y ) =/= y ) }
  assume subfacp1lem1.n: |- ( ph -> N e. NN )
  assume subfacp1lem1.m: |- ( ph -> M e. ( 2 ... ( N + 1 ) ) )
  assume subfacp1lem1.x: |- M e. _V
  assume subfacp1lem1.k: |- K = ( ( 2 ... ( N + 1 ) ) \ { M } )
  assume subfacp1lem2.5: |- F = ( G u. { <. 1 , M >. , <. M , 1 >. } )
  assume subfacp1lem2.6: |- ( ph -> G : K -1-1-onto-> K )

  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint N f
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint D n
  disjoint K f
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M f
  disjoint M x
  disjoint M y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint f g
  disjoint f h
  disjoint f m
  disjoint f s
  disjoint f z
  disjoint g h
  disjoint g m
  disjoint g n
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint h m
  disjoint h n
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint A h
  disjoint m n
  disjoint m s
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n s
  disjoint n z
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b x
  disjoint b y
  disjoint F b
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint F c
  disjoint F g
  disjoint c h
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c z
  disjoint N c
  disjoint f k
  disjoint g k
  disjoint N g
  disjoint h k
  disjoint N h
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint N k
  disjoint N m
  disjoint N z
  disjoint b k
  disjoint b m
  disjoint b n
  disjoint b h
  disjoint b s
  disjoint b z
  disjoint B b
  disjoint c s
  disjoint B c
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C b
  disjoint C c
  disjoint C x
  disjoint C y
  disjoint b ph
  disjoint c ph
  disjoint K c
  disjoint M b
  disjoint M g
  disjoint S m
  disjoint V f
  assert |- ( ph -> ( F : ( 1 ... ( N + 1 ) ) -1-1-onto-> ( 1 ... ( N + 1 ) ) /\ ( F ` 1 ) = M /\ ( F ` M ) = 1 ) )

  proof
    wph
    c1
    cN
    c1
    caddc
    co
    cfz
    co
    #
    @0
    cF
    wf1o
    #
    c1
    cF
    cfv
    #
    cM
    wceq
    cM
    cF
    cfv
    #
    c1
    wceq
    wph
    cK
    c1
    cM
    cpr
    #
    cun
    #
    @5
    cG
    c1
    cM
    cop
    #
    cM
    c1
    cop
    #
    cpr
    #
    cun
    #
    wf1o
    #
    @1
    wph
    cK
    cK
    cG
    wf1o
    @4
    @4
    @8
    wf1o
    #
    cK
    @4
    cin
    c0
    wceq
    #
    @12
    @10
    subfacp1lem2.6
    @11
    wph
    c1
    cz
    wcel
    cM
    cvv
    wcel
    @11
    1z
    subfacp1lem1.x
    c1
    cM
    cz
    cvv
    f1oprswap
    mp2an
    a1i
    wph
    @12
    @5
    @0
    wceq
    #
    cK
    chash
    cfv
    cN
    c1
    cmin
    co
    wceq
    #
    wph
    vx
    vy
    cA
    cD
    cS
    vf
    vn
    cK
    cM
    cN
    derang.d
    subfac.n
    subfacp1lem.a
    subfacp1lem1.n
    subfacp1lem1.m
    subfacp1lem1.x
    subfacp1lem1.k
    subfacp1lem1
    #
    simp1d
    #
    @16
    cK
    cK
    @4
    @4
    cG
    @8
    f1oun
    syl22anc
    wph
    @13
    @10
    @1
    wb
    wph
    @12
    @13
    @14
    @15
    simp2d
    @13
    @10
    @0
    @5
    cF
    wf1o
    #
    @1
    @10
    @5
    @5
    cF
    wf1o
    #
    @13
    @17
    cF
    @9
    wceq
    @18
    @10
    wb
    subfacp1lem2.5
    @5
    @5
    cF
    @9
    f1oeq1
    ax-mp
    @5
    @0
    @5
    cF
    f1oeq2
    syl5bbr
    @5
    @0
    @0
    cF
    f1oeq3
    bitrd
    syl
    mpbid
    #
    wph
    @2
    c1
    @6
    csn
    #
    cfv
    #
    cM
    wph
    cF
    wfun
    #
    @2
    @21
    wceq
    #
    wph
    @1
    @22
    @19
    @0
    @0
    cF
    f1ofun
    syl
    #
    @22
    @20
    cF
    wss
    c1
    @20
    cdm
    #
    wcel
    @23
    @20
    @8
    cF
    @6
    @7
    snsspr1
    @8
    @9
    cF
    @8
    cG
    ssun2
    subfacp1lem2.5
    sseqtr4i
    #
    sstri
    c1
    c1
    csn
    @25
    c1
    1ex
    snid
    c1
    cM
    subfacp1lem1.x
    dmsnop
    eleqtrri
    c1
    cF
    @20
    funssfv
    mp3an23
    syl
    c1
    cM
    1ex
    subfacp1lem1.x
    fvsn
    syl6eq
    wph
    @3
    cM
    @7
    csn
    #
    cfv
    #
    c1
    wph
    @22
    @3
    @28
    wceq
    #
    @24
    @22
    @27
    cF
    wss
    cM
    @27
    cdm
    #
    wcel
    @29
    @27
    @8
    cF
    @6
    @7
    snsspr2
    @26
    sstri
    cM
    cM
    csn
    @30
    cM
    subfacp1lem1.x
    snid
    cM
    c1
    1ex
    dmsnop
    eleqtrri
    cM
    cF
    @27
    funssfv
    mp3an23
    syl
    cM
    c1
    subfacp1lem1.x
    1ex
    fvsn
    syl6eq
    3jca
end
