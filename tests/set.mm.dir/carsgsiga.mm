include "ccarsg.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "wcel.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cuni.mm"
include "wi.mm"
include "w3a.mm"
include "wa.mm"
include "csiga.mm"
include "carsgcl.mm"
include "baselcarsg.mm"
include "adantr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "simpr.mm"
include "difelcarsg.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "c0.mm"
include "wceq.mm"
include "cesum.mm"
include "cle.mm"
include "3adant1r.mm"
include "elpwi.mm"
include "ad2antlr.mm"
include "carsgclctun.mm"
include "ex.mm"
include "3jca.mm"
include "jca.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "issiga.mm"
include "ax-mp.mm"
include "sylibr.mm"

theorem carsgsiga
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  let cA: class A
  let vb: setvar b
  let vf: setvar f
  let cE: class E
  let vk: setvar k
  let vn: setvar n
  let vz: setvar z
  let vg: setvar g
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume carsgsiga.1: |- ( ph -> ( M ` (/) ) = 0 )
  assume carsgsiga.2: |- ( ( ph /\ x ~<_ _om /\ x C_ ~P O ) -> ( M ` U. x ) <_ sum* y e. x ( M ` y ) )
  assume carsgsiga.3: |- ( ( ph /\ x C_ y /\ y e. ~P O ) -> ( M ` x ) <_ ( M ` y ) )

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
  disjoint A x
  disjoint A y
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
  disjoint f k
  disjoint f n
  disjoint f z
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint A g
  disjoint A k
  disjoint A n
  disjoint e g
  disjoint e k
  disjoint e n
  disjoint f g
  disjoint g k
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint E f
  disjoint E g
  disjoint E k
  disjoint E n
  disjoint M g
  disjoint M k
  disjoint M n
  disjoint O g
  disjoint O n
  disjoint g ph
  disjoint k ph
  disjoint n ph
  assert |- ( ph -> ( toCaraSiga ` M ) e. ( sigAlgebra ` O ) )

  proof
    wph
    cM
    ccarsg
    cfv
    #
    cO
    cpw
    #
    wss
    #
    cO
    @0
    wcel
    #
    cO
    vg
    cv
    #
    cdif
    @0
    wcel
    #
    vg
    @0
    wral
    #
    @4
    com
    cdom
    wbr
    #
    @4
    cuni
    @0
    wcel
    #
    wi
    #
    vg
    @0
    cpw
    #
    wral
    #
    w3a
    #
    wa
    #
    @0
    cO
    csiga
    cfv
    wcel
    #
    wph
    @2
    @12
    wph
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    carsgcl
    wph
    @3
    @6
    @11
    wph
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    carsgsiga.1
    baselcarsg
    wph
    @5
    vg
    @0
    wph
    @4
    @0
    wcel
    #
    wa
    @4
    cM
    cO
    cV
    wph
    cO
    cV
    wcel
    #
    @15
    carsgval.1
    adantr
    wph
    @1
    cc0
    cpnf
    cicc
    co
    cM
    wf
    #
    @15
    carsgval.2
    adantr
    wph
    @15
    simpr
    difelcarsg
    ralrimiva
    wph
    @9
    vg
    @10
    wph
    @4
    @10
    wcel
    #
    wa
    #
    @7
    @8
    @19
    @7
    wa
    vx
    vy
    @4
    cM
    cO
    cV
    wph
    @16
    @18
    @7
    carsgval.1
    ad2antrr
    wph
    @17
    @18
    @7
    carsgval.2
    ad2antrr
    wph
    c0
    cM
    cfv
    cc0
    wceq
    @18
    @7
    carsgsiga.1
    ad2antrr
    @19
    vx
    cv
    #
    com
    cdom
    wbr
    #
    @20
    @1
    wss
    #
    @20
    cuni
    cM
    cfv
    @20
    vy
    cv
    #
    cM
    cfv
    #
    vy
    cesum
    cle
    wbr
    #
    @7
    wph
    @21
    @22
    @25
    @18
    carsgsiga.2
    3adant1r
    3adant1r
    @19
    @20
    @23
    wss
    #
    @23
    @1
    wcel
    #
    @20
    cM
    cfv
    @24
    cle
    wbr
    #
    @7
    wph
    @26
    @27
    @28
    @18
    carsgsiga.3
    3adant1r
    3adant1r
    @19
    @7
    simpr
    @18
    @4
    @0
    wss
    wph
    @7
    @4
    @0
    elpwi
    ad2antlr
    carsgclctun
    ex
    ralrimiva
    3jca
    jca
    @0
    cvv
    wcel
    @14
    @13
    wb
    cM
    ccarsg
    fvex
    vg
    @0
    cO
    issiga
    ax-mp
    sylibr
end
