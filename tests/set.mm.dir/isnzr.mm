include "cv.mm"
include "cur.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "crg.mm"
include "cnzr.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "neeq12d.mm"
include "df-nzr.mm"
include "elrab2.mm"

theorem isnzr
  let cR: class R
  let c.1: class .1.
  let c.0: class .0.
  let vr: setvar r
  assume isnzr.o: |- .1. = ( 1r ` R )
  assume isnzr.z: |- .0. = ( 0g ` R )


  assert |- ( R e. NzRing <-> ( R e. Ring /\ .1. =/= .0. ) )

  proof
    vr
    cv
    #
    cur
    cfv
    #
    @0
    c0g
    cfv
    #
    wne
    c.1
    c.0
    wne
    vr
    cR
    crg
    cnzr
    @0
    cR
    wceq
    #
    @1
    c.1
    @2
    c.0
    @3
    @1
    cR
    cur
    cfv
    c.1
    @0
    cR
    cur
    fveq2
    isnzr.o
    syl6eqr
    @3
    @2
    cR
    c0g
    cfv
    c.0
    @0
    cR
    c0g
    fveq2
    isnzr.z
    syl6eqr
    neeq12d
    vr
    df-nzr
    elrab2
end
