include "cv.mm"
include "cfv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "chil.mm"
include "c0h.mm"
include "cdif.mm"
include "crab.mm"
include "cei.mm"
include "cvv.mm"
include "wcel.mm"
include "ax-hilex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "rabex.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "rabbidv.mm"
include "df-eigvec.mm"
include "fvmptmap.mm"

theorem eigvecval
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
  assert |- ( T : ~H --> ~H -> ( eigvec ` T ) = { x e. ( ~H \ 0H ) | E. y e. CC ( T ` x ) = ( y .h x ) } )

  proof
    vt
    cT
    vx
    cv
    #
    vt
    cv
    #
    cfv
    #
    vy
    cv
    @0
    csm
    co
    #
    wceq
    #
    vy
    cc
    wrex
    #
    vx
    chil
    c0h
    cdif
    #
    crab
    @0
    cT
    cfv
    #
    @3
    wceq
    #
    vy
    cc
    wrex
    #
    vx
    @6
    crab
    chil
    chil
    cei
    @9
    vx
    @6
    chil
    cvv
    wcel
    @6
    cvv
    wcel
    ax-hilex
    chil
    c0h
    cvv
    difexg
    ax-mp
    rabex
    ax-hilex
    ax-hilex
    @1
    cT
    wceq
    #
    @5
    @9
    vx
    @6
    @10
    @4
    @8
    vy
    cc
    @10
    @2
    @7
    @3
    @0
    @1
    cT
    fveq1
    eqeq1d
    rexbidv
    rabbidv
    vx
    vy
    vt
    df-eigvec
    fvmptmap
end
