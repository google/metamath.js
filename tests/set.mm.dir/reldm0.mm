include "wrel.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "cdm.mm"
include "rel0.mm"
include "eqrel.mm"
include "mpan2.mm"
include "wn.mm"
include "eq0.mm"
include "wex.mm"
include "alnex.mm"
include "vex.mm"
include "eldm2.mm"
include "xchbinxr.mm"
include "noel.mm"
include "nbn.mm"
include "albii.mm"
include "bitr3i.mm"
include "bitr2i.mm"
include "syl6bb.mm"

theorem reldm0
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( Rel A -> ( A = (/) <-> dom A = (/) ) )

  proof
    cA
    wrel
    #
    cA
    c0
    wceq
    #
    vx
    cv
    #
    vy
    cv
    cop
    #
    cA
    wcel
    #
    @3
    c0
    wcel
    #
    wb
    #
    vy
    wal
    #
    vx
    wal
    #
    cA
    cdm
    #
    c0
    wceq
    #
    @0
    c0
    wrel
    @1
    @8
    wb
    rel0
    vx
    vy
    cA
    c0
    eqrel
    mpan2
    @10
    @2
    @9
    wcel
    #
    wn
    #
    vx
    wal
    @8
    vx
    @9
    eq0
    @12
    @7
    vx
    @12
    @4
    wn
    #
    vy
    wal
    #
    @7
    @14
    @4
    vy
    wex
    @11
    @4
    vy
    alnex
    vy
    @2
    cA
    vx
    vex
    eldm2
    xchbinxr
    @13
    @6
    vy
    @5
    @4
    @3
    noel
    nbn
    albii
    bitr3i
    albii
    bitr2i
    syl6bb
end
