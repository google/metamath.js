include "clf.mm"
include "wcel.mm"
include "cc.mm"
include "chil.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csm.mm"
include "cva.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wf.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "ralbidv.mm"
include "2ralbidv.mm"
include "df-lnfn.mm"
include "elrab2.mm"
include "cnex.mm"
include "ax-hilex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitri.mm"

theorem ellnfn
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
  assert |- ( T e. LinFn <-> ( T : ~H --> CC /\ A. x e. CC A. y e. ~H A. z e. ~H ( T ` ( ( x .h y ) +h z ) ) = ( ( x x. ( T ` y ) ) + ( T ` z ) ) ) )

  proof
    cT
    clf
    wcel
    cT
    cc
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
    cmul
    co
    #
    @4
    cT
    cfv
    #
    caddc
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
    cc
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
    cmul
    co
    #
    @4
    @15
    cfv
    #
    caddc
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
    clf
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
    caddc
    @23
    @17
    @7
    @2
    cmul
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
    df-lnfn
    elrab2
    @1
    @14
    @13
    cc
    chil
    cT
    cnex
    ax-hilex
    elmap
    anbi1i
    bitri
end
