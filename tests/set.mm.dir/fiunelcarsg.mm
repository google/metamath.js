include "cv.mm"
include "cuni.mm"
include "ccarsg.mm"
include "cfv.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "unieq.mm"
include "eqidd.mm"
include "eleq12d.mm"
include "cdif.mm"
include "uni0.mm"
include "difid.mm"
include "eqtr4i.mm"
include "baselcarsg.mm"
include "difelcarsg.mm"
include "syl5eqel.mm"
include "wss.mm"
include "wa.mm"
include "uniun.mm"
include "vex.mm"
include "unisn.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "ad2antrr.mm"
include "cpw.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "simpr.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "simpll.mm"
include "carsgsigalem.mm"
include "syl3an1.mm"
include "simplrr.mm"
include "eldifad.mm"
include "sseldd.mm"
include "unelcarsg.mm"
include "ex.mm"
include "findcard2d.mm"

theorem fiunelcarsg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  let vb: setvar b
  let vf: setvar f
  let cE: class E
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume carsgsiga.1: |- ( ph -> ( M ` (/) ) = 0 )
  assume carsgsiga.2: |- ( ( ph /\ x ~<_ _om /\ x C_ ~P O ) -> ( M ` U. x ) <_ sum* y e. x ( M ` y ) )
  assume fiunelcarsg.1: |- ( ph -> A e. Fin )
  assume fiunelcarsg.2: |- ( ph -> A C_ ( toCaraSiga ` M ) )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint M x
  disjoint M y
  disjoint O x
  disjoint O y
  disjoint ph x
  disjoint ph y
  disjoint M a
  disjoint M e
  disjoint M m
  disjoint a e
  disjoint a m
  disjoint e m
  disjoint O a
  disjoint O e
  disjoint O m
  disjoint a ph
  disjoint e ph
  disjoint m ph
  disjoint A a
  disjoint A e
  disjoint A b
  disjoint A f
  disjoint a b
  disjoint a f
  disjoint a x
  disjoint a y
  disjoint b e
  disjoint b f
  disjoint b x
  disjoint b y
  disjoint e f
  disjoint e x
  disjoint e y
  disjoint f x
  disjoint f y
  disjoint E a
  disjoint E b
  disjoint E e
  disjoint E x
  disjoint E y
  disjoint M b
  disjoint M f
  disjoint O f
  disjoint b ph
  disjoint f ph
  assert |- ( ph -> U. A e. ( toCaraSiga ` M ) )

  proof
    wph
    va
    cv
    #
    cuni
    #
    cM
    ccarsg
    cfv
    #
    wcel
    c0
    cuni
    #
    @2
    wcel
    vb
    cv
    #
    cuni
    #
    @2
    wcel
    #
    @4
    vx
    cv
    #
    csn
    #
    cun
    #
    cuni
    #
    @2
    wcel
    #
    cA
    cuni
    #
    @2
    wcel
    va
    vb
    vx
    cA
    @0
    c0
    wceq
    #
    @1
    @3
    @2
    @2
    @0
    c0
    unieq
    @13
    @2
    eqidd
    eleq12d
    @0
    @4
    wceq
    #
    @1
    @5
    @2
    @2
    @0
    @4
    unieq
    @14
    @2
    eqidd
    eleq12d
    @0
    @9
    wceq
    #
    @1
    @10
    @2
    @2
    @0
    @9
    unieq
    @15
    @2
    eqidd
    eleq12d
    @0
    cA
    wceq
    #
    @1
    @12
    @2
    @2
    @0
    cA
    unieq
    @16
    @2
    eqidd
    eleq12d
    wph
    @3
    cO
    cO
    cdif
    #
    @2
    @3
    c0
    @17
    uni0
    cO
    difid
    eqtr4i
    wph
    cO
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    wph
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    carsgsiga.1
    baselcarsg
    difelcarsg
    syl5eqel
    wph
    @4
    cA
    wss
    #
    @7
    cA
    @4
    cdif
    wcel
    #
    wa
    #
    wa
    #
    @6
    @11
    @21
    @6
    wa
    #
    @10
    @5
    @7
    cun
    #
    @2
    @10
    @5
    @8
    cuni
    #
    cun
    @23
    @4
    @8
    uniun
    @24
    @7
    @5
    @7
    vx
    vex
    unisn
    uneq2i
    eqtri
    @22
    @5
    @7
    cM
    cO
    cV
    ve
    vf
    wph
    cO
    cV
    wcel
    @20
    @6
    carsgval.1
    ad2antrr
    wph
    cO
    cpw
    #
    cc0
    cpnf
    cicc
    co
    cM
    wf
    @20
    @6
    carsgval.2
    ad2antrr
    @21
    @6
    simpr
    @22
    wph
    ve
    cv
    #
    @25
    wcel
    vf
    cv
    #
    @25
    wcel
    @26
    @27
    cun
    cM
    cfv
    @26
    cM
    cfv
    @27
    cM
    cfv
    cxad
    co
    cle
    wbr
    wph
    @20
    @6
    simpll
    wph
    vx
    vy
    ve
    vf
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    carsgsiga.1
    carsgsiga.2
    carsgsigalem
    syl3an1
    @22
    cA
    @2
    @7
    wph
    cA
    @2
    wss
    @20
    @6
    fiunelcarsg.2
    ad2antrr
    @22
    @7
    cA
    @4
    wph
    @18
    @19
    @6
    simplrr
    eldifad
    sseldd
    unelcarsg
    syl5eqel
    ex
    fiunelcarsg.1
    findcard2d
end
