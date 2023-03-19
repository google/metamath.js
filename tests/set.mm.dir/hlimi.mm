include "chli.mm"
include "wbr.mm"
include "cvv.mm"
include "wcel.mm"
include "cn.mm"
include "chil.mm"
include "wf.mm"
include "wa.mm"
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
include "df-hlim.mm"
include "relopabi.mm"
include "brrelexi.mm"
include "nnex.mm"
include "fex.mm"
include "mpan2.mm"
include "ad2antrr.mm"
include "wb.mm"
include "wceq.mm"
include "feq1.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "fveq1.mm"
include "oveq12.mm"
include "sylan.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rexralbidv.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "brabga.mm"
include "pm5.21nii.mm"

theorem hlimi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cF: class F
  let vw: setvar w
  let vf: setvar f
  let cB: class B
  assume hlim.1: |- A e. _V

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
  disjoint f x
  disjoint w y
  disjoint f y
  disjoint w z
  disjoint f z
  disjoint f w
  disjoint F w
  disjoint F f
  disjoint A w
  disjoint A f
  disjoint B x
  disjoint B y
  disjoint B z
  assert |- ( F ~~>v A <-> ( ( F : NN --> ~H /\ A e. ~H ) /\ A. x e. RR+ E. y e. NN A. z e. ( ZZ>= ` y ) ( normh ` ( ( F ` z ) -h A ) ) < x ) )

  proof
    cF
    cA
    chli
    wbr
    #
    cF
    cvv
    wcel
    #
    cn
    chil
    cF
    wf
    #
    cA
    chil
    wcel
    #
    wa
    #
    vz
    cv
    #
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
    wa
    #
    cF
    cA
    chli
    cn
    chil
    vf
    cv
    #
    wf
    #
    vw
    cv
    #
    chil
    wcel
    #
    wa
    #
    @5
    @15
    cfv
    #
    @17
    cmv
    co
    #
    cno
    cfv
    #
    @9
    clt
    wbr
    #
    vz
    @11
    wral
    vy
    cn
    wrex
    #
    vx
    crp
    wral
    #
    wa
    #
    vf
    vw
    chli
    vx
    vy
    vz
    vw
    vf
    df-hlim
    #
    relopabi
    brrelexi
    @2
    @1
    @3
    @13
    @2
    cn
    cvv
    wcel
    @1
    nnex
    cn
    chil
    cvv
    cF
    fex
    mpan2
    ad2antrr
    @1
    cA
    cvv
    wcel
    @0
    @14
    wb
    hlim.1
    @26
    @14
    vf
    vw
    cF
    cA
    chli
    cvv
    cvv
    @15
    cF
    wceq
    #
    @17
    cA
    wceq
    #
    wa
    #
    @19
    @4
    @25
    @13
    @28
    @16
    @2
    @29
    @18
    @3
    cn
    chil
    @15
    cF
    feq1
    @17
    cA
    chil
    eleq1
    bi2anan9
    @30
    @24
    @12
    vx
    crp
    @30
    @23
    @10
    vy
    vz
    cn
    @11
    @30
    @22
    @8
    @9
    clt
    @30
    @21
    @7
    cno
    @28
    @20
    @6
    wceq
    @29
    @21
    @7
    wceq
    @5
    @15
    cF
    fveq1
    @20
    @6
    @17
    cA
    cmv
    oveq12
    sylan
    fveq2d
    breq1d
    rexralbidv
    ralbidv
    anbi12d
    @27
    brabga
    mpan2
    pm5.21nii
end
