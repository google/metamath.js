include "cv.mm"
include "cno.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "wceq.mm"
include "wa.mm"
include "chil.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cc.mm"
include "cnmf.mm"
include "xrltso.mm"
include "supex.mm"
include "ax-hilex.mm"
include "cnex.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "supeq1d.mm"
include "df-nmfn.mm"
include "fvmptmap.mm"

theorem nmfnval
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
  assert |- ( T : ~H --> CC -> ( normfn ` T ) = sup ( { x | E. y e. ~H ( ( normh ` y ) <_ 1 /\ x = ( abs ` ( T ` y ) ) ) } , RR* , < ) )

  proof
    vt
    cT
    vy
    cv
    #
    cno
    cfv
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @0
    vt
    cv
    #
    cfv
    #
    cabs
    cfv
    #
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    @1
    @2
    @0
    cT
    cfv
    #
    cabs
    cfv
    #
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    chil
    cc
    cnmf
    cxr
    @15
    clt
    xrltso
    supex
    ax-hilex
    cnex
    @3
    cT
    wceq
    #
    cxr
    @9
    @15
    clt
    @16
    @8
    @14
    vx
    @16
    @7
    @13
    vy
    chil
    @16
    @6
    @12
    @1
    @16
    @5
    @11
    @2
    @16
    @4
    @10
    cabs
    @0
    @3
    cT
    fveq1
    fveq2d
    eqeq2d
    anbi2d
    rexbidv
    abbidv
    supeq1d
    vx
    vy
    vt
    df-nmfn
    fvmptmap
end
