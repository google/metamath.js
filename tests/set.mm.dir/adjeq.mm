include "cado.mm"
include "wfun.mm"
include "chil.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cop.mm"
include "wcel.mm"
include "funadj.mm"
include "wa.mm"
include "copab.mm"
include "df-adjh.mm"
include "eleq2i.mm"
include "cvv.mm"
include "wb.mm"
include "ax-hilex.mm"
include "fex.mm"
include "mpan2.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "3anbi13d.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "3anbi23d.mm"
include "opelopabg.mm"
include "syl2an.mm"
include "syl5bb.mm"
include "df-3an.mm"
include "baibr.mm"
include "bitr4d.mm"
include "biimp3ar.mm"
include "funopfv.mm"
include "mpsyl.mm"

theorem adjeq
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cT: class T
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint x y
  disjoint S x
  disjoint S y
  disjoint T x
  disjoint T y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint S w
  disjoint S z
  disjoint T z
  disjoint T w
  assert |- ( ( T : ~H --> ~H /\ S : ~H --> ~H /\ A. x e. ~H A. y e. ~H ( ( T ` x ) .ih y ) = ( x .ih ( S ` y ) ) ) -> ( adjh ` T ) = S )

  proof
    cado
    wfun
    chil
    chil
    cT
    wf
    #
    chil
    chil
    cS
    wf
    #
    vx
    cv
    #
    cT
    cfv
    #
    vy
    cv
    #
    csp
    co
    #
    @2
    @4
    cS
    cfv
    #
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    #
    cT
    cS
    cop
    #
    cado
    wcel
    #
    cT
    cado
    cfv
    cS
    wceq
    funadj
    @0
    @1
    @12
    @9
    @0
    @1
    wa
    #
    @12
    @10
    @9
    @12
    @11
    chil
    chil
    vz
    cv
    #
    wf
    #
    chil
    chil
    vw
    cv
    #
    wf
    #
    @2
    @14
    cfv
    #
    @4
    csp
    co
    #
    @2
    @4
    @16
    cfv
    #
    csp
    co
    #
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    #
    vz
    vw
    copab
    #
    wcel
    #
    @13
    @10
    cado
    @25
    @11
    vx
    vy
    vw
    vz
    df-adjh
    eleq2i
    @0
    cT
    cvv
    wcel
    #
    cS
    cvv
    wcel
    #
    @26
    @10
    wb
    @1
    @0
    chil
    cvv
    wcel
    #
    @27
    ax-hilex
    chil
    chil
    cvv
    cT
    fex
    mpan2
    @1
    @29
    @28
    ax-hilex
    chil
    chil
    cvv
    cS
    fex
    mpan2
    @24
    @0
    @17
    @5
    @21
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    w3a
    @10
    vz
    vw
    cT
    cS
    cvv
    cvv
    @14
    cT
    wceq
    #
    @15
    @0
    @23
    @31
    @17
    chil
    chil
    @14
    cT
    feq1
    @32
    @22
    @30
    vx
    vy
    chil
    chil
    @32
    @19
    @5
    @21
    @32
    @18
    @3
    @4
    csp
    @2
    @14
    cT
    fveq1
    oveq1d
    eqeq1d
    2ralbidv
    3anbi13d
    @16
    cS
    wceq
    #
    @17
    @1
    @31
    @9
    @0
    chil
    chil
    @16
    cS
    feq1
    @33
    @30
    @8
    vx
    vy
    chil
    chil
    @33
    @21
    @7
    @5
    @33
    @20
    @6
    @2
    csp
    @4
    @16
    cS
    fveq1
    oveq2d
    eqeq2d
    2ralbidv
    3anbi23d
    opelopabg
    syl2an
    syl5bb
    @10
    @13
    @9
    @0
    @1
    @9
    df-3an
    baibr
    bitr4d
    biimp3ar
    cT
    cS
    cado
    funopfv
    mpsyl
end
