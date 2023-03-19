include "cur.mm"
include "cfv.mm"
include "wceq.mm"
include "wtru.mm"
include "cbs.mm"
include "eqidd.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cps1.mm"
include "eqid.mm"
include "ply1bas.mm"
include "fveq2i.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "ply1mulr.mm"
include "oveqdr.mm"
include "rngidpropd.mm"
include "trud.mm"
include "eqtri.mm"

theorem ply1mpl1
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  assume ply1mpl1.m: |- M = ( 1o mPoly R )
  assume ply1mpl1.p: |- P = ( Poly1 ` R )
  assume ply1mpl1.o: |- .1. = ( 1r ` P )


  assert |- .1. = ( 1r ` M )

  proof
    c.1
    cP
    cur
    cfv
    #
    cM
    cur
    cfv
    #
    ply1mpl1.o
    @0
    @1
    wceq
    wtru
    vx
    vy
    cP
    cbs
    cfv
    #
    cP
    cM
    wtru
    @2
    eqidd
    @2
    cM
    cbs
    cfv
    #
    wceq
    wtru
    @2
    c1o
    cR
    cmpl
    co
    #
    cbs
    cfv
    @3
    cP
    cR
    cR
    cps1
    cfv
    #
    @2
    ply1mpl1.p
    @5
    eqid
    @2
    eqid
    ply1bas
    cM
    @4
    cbs
    ply1mpl1.m
    fveq2i
    eqtr4i
    a1i
    wtru
    vx
    cv
    @2
    wcel
    vy
    cv
    @2
    wcel
    wa
    vx
    vy
    cP
    cmulr
    cfv
    #
    cM
    cmulr
    cfv
    #
    @6
    @7
    wceq
    wtru
    cR
    cM
    @6
    cP
    ply1mpl1.p
    ply1mpl1.m
    @6
    eqid
    ply1mulr
    a1i
    oveqdr
    rngidpropd
    trud
    eqtri
end
