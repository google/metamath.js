include "cv.mm"
include "cei.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cno.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmpt.mm"
include "chil.mm"
include "cel.mm"
include "fvex.mm"
include "mptex.mm"
include "ax-hilex.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1.mm"
include "oveq1d.mm"
include "mpteq12dv.mm"
include "df-eigval.mm"
include "fvmptmap.mm"

theorem eigvalfval
  let vx: setvar x
  let cT: class T
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z

  disjoint T x
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
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint T y
  disjoint T z
  assert |- ( T : ~H --> ~H -> ( eigval ` T ) = ( x e. ( eigvec ` T ) |-> ( ( ( T ` x ) .ih x ) / ( ( normh ` x ) ^ 2 ) ) ) )

  proof
    vt
    cT
    vx
    vt
    cv
    #
    cei
    cfv
    #
    vx
    cv
    #
    @0
    cfv
    #
    @2
    csp
    co
    #
    @2
    cno
    cfv
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cmpt
    vx
    cT
    cei
    cfv
    #
    @2
    cT
    cfv
    #
    @2
    csp
    co
    #
    @5
    cdiv
    co
    #
    cmpt
    chil
    chil
    cel
    vx
    @7
    @10
    cT
    cei
    fvex
    mptex
    ax-hilex
    ax-hilex
    @0
    cT
    wceq
    #
    vx
    @1
    @6
    @7
    @10
    @0
    cT
    cei
    fveq2
    @11
    @4
    @9
    @5
    cdiv
    @11
    @3
    @8
    @2
    csp
    @2
    @0
    cT
    fveq1
    oveq1d
    oveq1d
    mpteq12dv
    vx
    vt
    df-eigval
    fvmptmap
end
