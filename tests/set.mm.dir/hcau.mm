include "ccau.mm"
include "wcel.mm"
include "chil.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmv.mm"
include "cno.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "wf.mm"
include "wceq.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rexralbidv.mm"
include "ralbidv.mm"
include "df-hcau.mm"
include "elrab2.mm"
include "ax-hilex.mm"
include "nnex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem hcau
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let vf: setvar f
  let cA: class A

  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- ( F e. Cauchy <-> ( F : NN --> ~H /\ A. x e. RR+ E. y e. NN A. z e. ( ZZ>= ` y ) ( normh ` ( ( F ` y ) -h ( F ` z ) ) ) < x ) )

  proof
    cF
    ccau
    wcel
    cF
    chil
    cn
    cmap
    co
    #
    wcel
    #
    vy
    cv
    #
    cF
    cfv
    #
    vz
    cv
    #
    cF
    cfv
    #
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
    @2
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
    cn
    chil
    cF
    wf
    #
    @12
    wa
    @2
    vf
    cv
    #
    cfv
    #
    @4
    @14
    cfv
    #
    cmv
    co
    #
    cno
    cfv
    #
    @8
    clt
    wbr
    #
    vz
    @10
    wral
    vy
    cn
    wrex
    #
    vx
    crp
    wral
    @12
    vf
    cF
    @0
    ccau
    @14
    cF
    wceq
    #
    @20
    @11
    vx
    crp
    @21
    @19
    @9
    vy
    vz
    cn
    @10
    @21
    @18
    @7
    @8
    clt
    @21
    @17
    @6
    cno
    @21
    @15
    @3
    @16
    @5
    cmv
    @2
    @14
    cF
    fveq1
    @4
    @14
    cF
    fveq1
    oveq12d
    fveq2d
    breq1d
    rexralbidv
    ralbidv
    vx
    vy
    vz
    vf
    df-hcau
    elrab2
    @1
    @13
    @12
    chil
    cn
    cF
    ax-hilex
    nnex
    elmap
    anbi1i
    bitri
end
