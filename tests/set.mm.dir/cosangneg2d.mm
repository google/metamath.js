include "cdiv.mm"
include "co.mm"
include "cre.mm"
include "cfv.mm"
include "cabs.mm"
include "cneg.mm"
include "ccos.mm"
include "divcld.mm"
include "recld.mm"
include "recnd.mm"
include "abscld.mm"
include "divne0d.mm"
include "absne0d.mm"
include "divnegd.mm"
include "clog.mm"
include "cim.mm"
include "angvald.mm"
include "fveq2d.mm"
include "cosargd.mm"
include "eqtrd.mm"
include "negeqd.mm"
include "negcld.mm"
include "negne0d.mm"
include "renegd.mm"
include "eqtr3d.mm"
include "absnegd.mm"
include "oveq12d.mm"
include "3eqtrd.mm"
include "3eqtr4rd.mm"

theorem cosangneg2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cX: class X
  let cY: class Y
  let cA: class A
  let cB: class B
  let cC: class C
  assume ang.1: |- F = ( x e. ( CC \ { 0 } ) , y e. ( CC \ { 0 } ) |-> ( Im ` ( log ` ( y / x ) ) ) )
  assume cosangneg2d.1: |- ( ph -> X e. CC )
  assume cosangneg2d.2: |- ( ph -> X =/= 0 )
  assume cosangneg2d.3: |- ( ph -> Y e. CC )
  assume cosangneg2d.4: |- ( ph -> Y =/= 0 )

  disjoint x y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  assert |- ( ph -> ( cos ` ( X F -u Y ) ) = -u ( cos ` ( X F Y ) ) )

  proof
    wph
    cY
    cX
    cdiv
    co
    #
    cre
    cfv
    #
    @0
    cabs
    cfv
    #
    cdiv
    co
    #
    cneg
    @1
    cneg
    #
    @2
    cdiv
    co
    #
    cX
    cY
    cF
    co
    #
    ccos
    cfv
    #
    cneg
    cX
    cY
    cneg
    #
    cF
    co
    #
    ccos
    cfv
    #
    wph
    @1
    @2
    wph
    @1
    wph
    @0
    wph
    cY
    cX
    cosangneg2d.3
    cosangneg2d.1
    cosangneg2d.2
    divcld
    #
    recld
    recnd
    wph
    @2
    wph
    @0
    @11
    abscld
    recnd
    wph
    @0
    @11
    wph
    cY
    cX
    cosangneg2d.3
    cosangneg2d.1
    cosangneg2d.4
    cosangneg2d.2
    divne0d
    #
    absne0d
    divnegd
    wph
    @7
    @3
    wph
    @7
    @0
    clog
    cfv
    cim
    cfv
    #
    ccos
    cfv
    @3
    wph
    @6
    @13
    ccos
    wph
    vx
    vy
    cF
    cX
    cY
    ang.1
    cosangneg2d.1
    cosangneg2d.2
    cosangneg2d.3
    cosangneg2d.4
    angvald
    fveq2d
    wph
    @0
    @11
    @12
    cosargd
    eqtrd
    negeqd
    wph
    @10
    @8
    cX
    cdiv
    co
    #
    clog
    cfv
    cim
    cfv
    #
    ccos
    cfv
    @14
    cre
    cfv
    #
    @14
    cabs
    cfv
    #
    cdiv
    co
    @5
    wph
    @9
    @15
    ccos
    wph
    vx
    vy
    cF
    cX
    @8
    ang.1
    cosangneg2d.1
    cosangneg2d.2
    wph
    cY
    cosangneg2d.3
    negcld
    #
    wph
    cY
    cosangneg2d.3
    cosangneg2d.4
    negne0d
    #
    angvald
    fveq2d
    wph
    @14
    wph
    @8
    cX
    @18
    cosangneg2d.1
    cosangneg2d.2
    divcld
    wph
    @8
    cX
    @18
    cosangneg2d.1
    @19
    cosangneg2d.2
    divne0d
    cosargd
    wph
    @16
    @4
    @17
    @2
    cdiv
    wph
    @0
    cneg
    #
    cre
    cfv
    @16
    @4
    wph
    @20
    @14
    cre
    wph
    cY
    cX
    cosangneg2d.3
    cosangneg2d.1
    cosangneg2d.2
    divnegd
    #
    fveq2d
    wph
    @0
    @11
    renegd
    eqtr3d
    wph
    @20
    cabs
    cfv
    @17
    @2
    wph
    @20
    @14
    cabs
    @21
    fveq2d
    wph
    @0
    @11
    absnegd
    eqtr3d
    oveq12d
    3eqtrd
    3eqtr4rd
end
