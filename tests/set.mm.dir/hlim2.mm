include "chil.mm"
include "wcel.mm"
include "cn.mm"
include "wf.mm"
include "chli.mm"
include "wbr.mm"
include "cv.mm"
include "cfv.mm"
include "cmv.mm"
include "co.mm"
include "cno.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wb.mm"
include "wi.mm"
include "wceq.mm"
include "breq2.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rexralbidv.mm"
include "ralbidv.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "wa.mm"
include "vex.mm"
include "hlimi.mm"
include "baib.mm"
include "expcom.mm"
include "vtoclga.mm"
include "impcom.mm"

theorem hlim2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint A w
  assert |- ( ( F : NN --> ~H /\ A e. ~H ) -> ( F ~~>v A <-> A. x e. RR+ E. y e. NN A. z e. ( ZZ>= ` y ) ( normh ` ( ( F ` z ) -h A ) ) < x ) )

  proof
    cA
    chil
    wcel
    cn
    chil
    cF
    wf
    #
    cF
    cA
    chli
    wbr
    #
    vz
    cv
    cF
    cfv
    #
    cA
    cmv
    co
    #
    cno
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vz
    vy
    cv
    cuz
    cfv
    #
    wral
    vy
    cn
    wrex
    #
    vx
    crp
    wral
    #
    wb
    #
    @0
    cF
    vw
    cv
    #
    chli
    wbr
    #
    @2
    @11
    cmv
    co
    #
    cno
    cfv
    #
    @5
    clt
    wbr
    #
    vz
    @7
    wral
    vy
    cn
    wrex
    #
    vx
    crp
    wral
    #
    wb
    #
    wi
    @0
    @10
    wi
    vw
    cA
    chil
    @11
    cA
    wceq
    #
    @18
    @10
    @0
    @19
    @12
    @1
    @17
    @9
    @11
    cA
    cF
    chli
    breq2
    @19
    @16
    @8
    vx
    crp
    @19
    @15
    @6
    vy
    vz
    cn
    @7
    @19
    @14
    @4
    @5
    clt
    @19
    @13
    @3
    cno
    @11
    cA
    @2
    cmv
    oveq2
    fveq2d
    breq1d
    rexralbidv
    ralbidv
    bibi12d
    imbi2d
    @0
    @11
    chil
    wcel
    #
    @18
    @12
    @0
    @20
    wa
    @17
    vx
    vy
    vz
    @11
    cF
    vw
    vex
    hlimi
    baib
    expcom
    vtoclga
    impcom
end
