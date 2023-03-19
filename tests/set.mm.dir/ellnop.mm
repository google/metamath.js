include "clo.mm"
include "wcel.mm"
include "chil.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csm.mm"
include "cva.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "cc.mm"
include "wa.mm"
include "wf.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "df-lnop.mm"
include "elrab2.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem ellnop
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w

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
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint T w
  assert |- ( T e. LinOp <-> ( T : ~H --> ~H /\ A. x e. CC A. y e. ~H A. z e. ~H ( T ` ( ( x .h y ) +h z ) ) = ( ( x .h ( T ` y ) ) +h ( T ` z ) ) ) )

  proof
    cT
    clo
    wcel
    cT
    chil
    chil
    cmap
    co
    #
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    csm
    co
    vz
    cv
    #
    cva
    co
    #
    cT
    cfv
    #
    @2
    @3
    cT
    cfv
    #
    csm
    co
    #
    @4
    cT
    cfv
    #
    cva
    co
    #
    wceq
    #
    vz
    chil
    wral
    #
    vy
    chil
    wral
    vx
    cc
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
    @5
    vt
    cv
    #
    cfv
    #
    @2
    @3
    @15
    cfv
    #
    csm
    co
    #
    @4
    @15
    cfv
    #
    cva
    co
    #
    wceq
    #
    vz
    chil
    wral
    #
    vy
    chil
    wral
    vx
    cc
    wral
    @13
    vt
    cT
    @0
    clo
    @15
    cT
    wceq
    #
    @22
    @12
    vx
    vy
    cc
    chil
    @23
    @21
    @11
    vz
    chil
    @23
    @16
    @6
    @20
    @10
    @5
    @15
    cT
    fveq1
    @23
    @18
    @8
    @19
    @9
    cva
    @23
    @17
    @7
    @2
    csm
    @3
    @15
    cT
    fveq1
    oveq2d
    @4
    @15
    cT
    fveq1
    oveq12d
    eqeq12d
    ralbidv
    2ralbidv
    vx
    vy
    vz
    vt
    df-lnop
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
