include "c0v.mm"
include "cfv.mm"
include "cno.mm"
include "cv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "chil.mm"
include "wrex.mm"
include "cab.mm"
include "wcel.mm"
include "ax-hv0cl.mm"
include "cc0.mm"
include "norm0.mm"
include "0le1.mm"
include "eqbrtri.mm"
include "eqid.mm"
include "pm3.2i.mm"
include "fveq2.mm"
include "breq1d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "fvex.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elab.mm"
include "mpbir.mm"

theorem nmopsetn0
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
  assert |- ( normh ` ( T ` 0h ) ) e. { x | E. y e. ~H ( ( normh ` y ) <_ 1 /\ x = ( normh ` ( T ` y ) ) ) }

  proof
    c0v
    cT
    cfv
    #
    cno
    cfv
    #
    vy
    cv
    #
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @2
    cT
    cfv
    #
    cno
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
    wcel
    @4
    @1
    @7
    wceq
    #
    wa
    #
    vy
    chil
    wrex
    #
    c0v
    chil
    wcel
    c0v
    cno
    cfv
    #
    c1
    cle
    wbr
    #
    @1
    @1
    wceq
    #
    wa
    #
    @13
    ax-hv0cl
    @15
    @16
    @14
    cc0
    c1
    cle
    norm0
    0le1
    eqbrtri
    @1
    eqid
    pm3.2i
    @12
    @17
    vy
    c0v
    chil
    @2
    c0v
    wceq
    #
    @4
    @15
    @11
    @16
    @18
    @3
    @14
    c1
    cle
    @2
    c0v
    cno
    fveq2
    breq1d
    @18
    @7
    @1
    @1
    @18
    @6
    @0
    cno
    @2
    c0v
    cT
    fveq2
    fveq2d
    eqeq2d
    anbi12d
    rspcev
    mp2an
    @10
    @13
    vx
    @1
    @0
    cno
    fvex
    @5
    @1
    wceq
    #
    @9
    @12
    vy
    chil
    @19
    @8
    @11
    @4
    @5
    @1
    @7
    eqeq1
    anbi2d
    rexbidv
    elab
    mpbir
end
