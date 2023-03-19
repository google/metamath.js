include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "ccnv.mm"
include "wf1o.mm"
include "wfn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "f1oi.mm"
include "a1i.mm"
include "subfacp1lem2a.mm"
include "simp1d.mm"
include "f1ocnv.mm"
include "f1ofn.mm"
include "3syl.mm"
include "syl.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wo.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "chash.mm"
include "cmin.mm"
include "subfacp1lem1.mm"
include "simp2d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "elun.mm"
include "sylib.mm"
include "subfacp1lem2b.mm"
include "fvresi.mm"
include "adantl.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "vex.mm"
include "elpr.mm"
include "simp3d.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibrcom.mm"
include "jaod.mm"
include "imp.mm"
include "sylan2b.mm"
include "jaodan.mm"
include "syldan.mm"
include "wi.mm"
include "adantr.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "f1ocnvfv.mm"
include "syl2anc.mm"
include "mpd.mm"
include "eqfnfvd.mm"

theorem subfacp1lem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let vf: setvar f
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cM: class M
  let cN: class N
  let vh: setvar h
  let vm: setvar m
  let vs: setvar s
  let vz: setvar z
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let cC: class C
  let cV: class V
  assume derang.d: |- D = ( x e. Fin |-> ( # ` { f | ( f : x -1-1-onto-> x /\ A. y e. x ( f ` y ) =/= y ) } ) )
  assume subfac.n: |- S = ( n e. NN0 |-> ( D ` ( 1 ... n ) ) )
  assume subfacp1lem.a: |- A = { f | ( f : ( 1 ... ( N + 1 ) ) -1-1-onto-> ( 1 ... ( N + 1 ) ) /\ A. y e. ( 1 ... ( N + 1 ) ) ( f ` y ) =/= y ) }
  assume subfacp1lem1.n: |- ( ph -> N e. NN )
  assume subfacp1lem1.m: |- ( ph -> M e. ( 2 ... ( N + 1 ) ) )
  assume subfacp1lem1.x: |- M e. _V
  assume subfacp1lem1.k: |- K = ( ( 2 ... ( N + 1 ) ) \ { M } )
  assume subfacp1lem5.b: |- B = { g e. A | ( ( g ` 1 ) = M /\ ( g ` M ) =/= 1 ) }
  assume subfacp1lem5.f: |- F = ( ( _I |` K ) u. { <. 1 , M >. , <. M , 1 >. } )

  disjoint f g
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint N f
  disjoint N g
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint B f
  disjoint B g
  disjoint B x
  disjoint B y
  disjoint ph x
  disjoint ph y
  disjoint D n
  disjoint K f
  disjoint K n
  disjoint K x
  disjoint K y
  disjoint M f
  disjoint M g
  disjoint M x
  disjoint M y
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint f h
  disjoint f m
  disjoint f s
  disjoint f z
  disjoint g h
  disjoint g m
  disjoint g s
  disjoint g z
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
  disjoint c h
  disjoint c k
  disjoint c m
  disjoint c n
  disjoint c z
  disjoint N c
  disjoint f k
  disjoint g k
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
  disjoint B h
  disjoint B s
  disjoint B z
  disjoint C b
  disjoint C c
  disjoint C x
  disjoint C y
  disjoint b ph
  disjoint c ph
  disjoint K c
  disjoint M b
  disjoint S m
  disjoint V f
  assert |- ( ph -> `' F = F )

  proof
    wph
    vx
    c1
    cN
    c1
    caddc
    co
    cfz
    co
    #
    cF
    ccnv
    #
    cF
    wph
    @0
    @0
    cF
    wf1o
    #
    @0
    @0
    @1
    wf1o
    @1
    @0
    wfn
    wph
    @2
    c1
    cF
    cfv
    #
    cM
    wceq
    #
    cM
    cF
    cfv
    #
    c1
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
    cF
    cid
    cK
    cres
    #
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
    subfacp1lem5.f
    cK
    cK
    @7
    wf1o
    wph
    cK
    f1oi
    a1i
    #
    subfacp1lem2a
    #
    simp1d
    #
    @0
    @0
    cF
    f1ocnv
    @0
    @0
    @1
    f1ofn
    3syl
    wph
    @2
    cF
    @0
    wfn
    @10
    @0
    @0
    cF
    f1ofn
    syl
    wph
    vx
    cv
    #
    @0
    wcel
    #
    wa
    #
    @11
    cF
    cfv
    #
    cF
    cfv
    #
    @11
    wceq
    #
    @11
    @1
    cfv
    @14
    wceq
    #
    wph
    @12
    @11
    cK
    wcel
    #
    @11
    c1
    cM
    cpr
    #
    wcel
    #
    wo
    #
    @16
    @13
    @11
    cK
    @19
    cun
    #
    wcel
    #
    @21
    wph
    @23
    @12
    wph
    @22
    @0
    @11
    wph
    cK
    @19
    cin
    c0
    wceq
    @22
    @0
    wceq
    cK
    chash
    cfv
    cN
    c1
    cmin
    co
    wceq
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
    simp2d
    eleq2d
    biimpar
    @11
    cK
    @19
    elun
    sylib
    wph
    @18
    @16
    @20
    wph
    @18
    wa
    #
    @15
    @14
    @11
    @24
    @14
    @11
    cF
    @24
    @14
    @11
    @7
    cfv
    #
    @11
    wph
    vx
    vy
    cA
    cD
    cS
    vf
    vn
    cF
    @7
    cK
    cM
    cN
    @11
    derang.d
    subfac.n
    subfacp1lem.a
    subfacp1lem1.n
    subfacp1lem1.m
    subfacp1lem1.x
    subfacp1lem1.k
    subfacp1lem5.f
    @8
    subfacp1lem2b
    @18
    @25
    @11
    wceq
    wph
    cK
    @11
    fvresi
    adantl
    eqtrd
    #
    fveq2d
    @26
    eqtrd
    @20
    wph
    @11
    c1
    wceq
    #
    @11
    cM
    wceq
    #
    wo
    #
    @16
    @11
    c1
    cM
    vx
    vex
    elpr
    wph
    @29
    @16
    wph
    @27
    @16
    @28
    wph
    @16
    @27
    @3
    cF
    cfv
    #
    c1
    wceq
    wph
    @30
    @5
    c1
    wph
    @3
    cM
    cF
    wph
    @2
    @4
    @6
    @9
    simp2d
    #
    fveq2d
    wph
    @2
    @4
    @6
    @9
    simp3d
    #
    eqtrd
    @27
    @15
    @30
    @11
    c1
    @27
    @14
    @3
    cF
    @11
    c1
    cF
    fveq2
    fveq2d
    @27
    id
    eqeq12d
    syl5ibrcom
    wph
    @16
    @28
    @5
    cF
    cfv
    #
    cM
    wceq
    wph
    @33
    @3
    cM
    wph
    @5
    c1
    cF
    @32
    fveq2d
    @31
    eqtrd
    @28
    @15
    @33
    @11
    cM
    @28
    @14
    @5
    cF
    @11
    cM
    cF
    fveq2
    fveq2d
    @28
    id
    eqeq12d
    syl5ibrcom
    jaod
    imp
    sylan2b
    jaodan
    syldan
    @13
    @2
    @14
    @0
    wcel
    @16
    @17
    wi
    wph
    @2
    @12
    @10
    adantr
    wph
    @0
    @0
    @11
    cF
    wph
    @2
    @0
    @0
    cF
    wf
    @10
    @0
    @0
    cF
    f1of
    syl
    ffvelrnda
    @0
    @0
    @14
    @11
    cF
    f1ocnvfv
    syl2anc
    mpd
    eqfnfvd
end
