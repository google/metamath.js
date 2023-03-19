include "ccop.mm"
include "wcel.mm"
include "chil.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "cmv.mm"
include "cno.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "wa.mm"
include "wf.mm"
include "wceq.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "imbi2d.mm"
include "rexralbidv.mm"
include "2ralbidv.mm"
include "df-cnop.mm"
include "elrab2.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem elcnop
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cT: class T
  let vt: setvar t
  let vu: setvar u

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint x y
  disjoint x z
  disjoint T x
  disjoint y z
  disjoint T y
  disjoint T z
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint T t
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint T u
  assert |- ( T e. ContOp <-> ( T : ~H --> ~H /\ A. x e. ~H A. y e. RR+ E. z e. RR+ A. w e. ~H ( ( normh ` ( w -h x ) ) < z -> ( normh ` ( ( T ` w ) -h ( T ` x ) ) ) < y ) ) )

  proof
    cT
    ccop
    wcel
    cT
    chil
    chil
    cmap
    co
    #
    wcel
    #
    vw
    cv
    #
    vx
    cv
    #
    cmv
    co
    cno
    cfv
    vz
    cv
    clt
    wbr
    #
    @2
    cT
    cfv
    #
    @3
    cT
    cfv
    #
    cmv
    co
    #
    cno
    cfv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wi
    #
    vw
    chil
    wral
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    chil
    wral
    #
    wa
    chil
    chil
    cT
    wf
    #
    @13
    wa
    @4
    @2
    vt
    cv
    #
    cfv
    #
    @3
    @15
    cfv
    #
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
    wi
    #
    vw
    chil
    wral
    vz
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    chil
    wral
    @13
    vt
    cT
    @0
    ccop
    @15
    cT
    wceq
    #
    @22
    @12
    vx
    vy
    chil
    crp
    @23
    @21
    @11
    vz
    vw
    crp
    chil
    @23
    @20
    @10
    @4
    @23
    @19
    @8
    @9
    clt
    @23
    @18
    @7
    cno
    @23
    @16
    @5
    @17
    @6
    cmv
    @2
    @15
    cT
    fveq1
    @3
    @15
    cT
    fveq1
    oveq12d
    fveq2d
    breq1d
    imbi2d
    rexralbidv
    2ralbidv
    vx
    vy
    vz
    vw
    vt
    df-cnop
    elrab2
    @1
    @14
    @13
    chil
    chil
    cT
    ax-hilex
    ax-hilex
    elmap
    anbi1i
    bitri
end
