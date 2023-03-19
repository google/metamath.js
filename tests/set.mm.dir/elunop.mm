include "cuo.mm"
include "wcel.mm"
include "cvv.mm"
include "chil.mm"
include "wfo.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "elex.mm"
include "wf.mm"
include "fof.mm"
include "ax-hilex.mm"
include "fex.mm"
include "sylancl.mm"
include "adantr.mm"
include "foeq1.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "df-unop.mm"
include "elab2g.mm"
include "pm5.21nii.mm"

theorem elunop
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z

  disjoint x y
  disjoint T x
  disjoint T y
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
  disjoint x z
  disjoint y z
  disjoint T z
  assert |- ( T e. UniOp <-> ( T : ~H -onto-> ~H /\ A. x e. ~H A. y e. ~H ( ( T ` x ) .ih ( T ` y ) ) = ( x .ih y ) ) )

  proof
    cT
    cuo
    wcel
    cT
    cvv
    wcel
    #
    chil
    chil
    cT
    wfo
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
    cT
    cfv
    #
    csp
    co
    #
    @2
    @4
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
    wa
    #
    cT
    cuo
    elex
    @1
    @0
    @9
    @1
    chil
    chil
    cT
    wf
    chil
    cvv
    wcel
    @0
    chil
    chil
    cT
    fof
    ax-hilex
    chil
    chil
    cvv
    cT
    fex
    sylancl
    adantr
    chil
    chil
    vt
    cv
    #
    wfo
    #
    @2
    @11
    cfv
    #
    @4
    @11
    cfv
    #
    csp
    co
    #
    @7
    wceq
    #
    vy
    chil
    wral
    vx
    chil
    wral
    #
    wa
    @10
    vt
    cT
    cuo
    cvv
    @11
    cT
    wceq
    #
    @12
    @1
    @17
    @9
    chil
    chil
    @11
    cT
    foeq1
    @18
    @16
    @8
    vx
    vy
    chil
    chil
    @18
    @15
    @6
    @7
    @18
    @13
    @3
    @14
    @5
    csp
    @2
    @11
    cT
    fveq1
    @4
    @11
    cT
    fveq1
    oveq12d
    eqeq1d
    2ralbidv
    anbi12d
    vx
    vy
    vt
    df-unop
    elab2g
    pm5.21nii
end
