include "crp.mm"
include "cr.mm"
include "cv.mm"
include "cchp.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "wcel.mm"
include "rpre.mm"
include "chpcl.mm"
include "syl.mm"
include "resubcld.mm"
include "fmpti.mm"

theorem pntrf
  let cR: class R
  let va: setvar a
  let vd: setvar d
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  assume pntrval.r: |- R = ( a e. RR+ |-> ( ( psi ` a ) - a ) )


  assert |- R : RR+ --> RR

  proof
    va
    crp
    cr
    va
    cv
    #
    cchp
    cfv
    #
    @0
    cmin
    co
    cR
    pntrval.r
    @0
    crp
    wcel
    #
    @1
    @0
    @2
    @0
    cr
    wcel
    @1
    cr
    wcel
    @0
    rpre
    #
    @0
    chpcl
    syl
    @3
    resubcld
    fmpti
end
