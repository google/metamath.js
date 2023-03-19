include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cdm.mm"
include "wceq.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "pjfval2.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem pjval
  let cP: class P
  let cT: class T
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume pjfval2.o: |- ._|_ = ( ocv ` W )
  assume pjfval2.p: |- P = ( proj1 ` W )
  assume pjfval2.k: |- K = ( proj ` W )


  assert |- ( T e. dom K -> ( K ` T ) = ( T P ( ._|_ ` T ) ) )

  proof
    vx
    cT
    vx
    cv
    #
    @0
    c.pe
    cfv
    #
    cP
    co
    cT
    cT
    c.pe
    cfv
    #
    cP
    co
    cK
    cdm
    cK
    @0
    cT
    wceq
    #
    @0
    cT
    @1
    @2
    cP
    @3
    id
    @0
    cT
    c.pe
    fveq2
    oveq12d
    vx
    cP
    cK
    c.pe
    cW
    pjfval2.o
    pjfval2.p
    pjfval2.k
    pjfval2
    cT
    @2
    cP
    ovex
    fvmpt
end
