include "c0g.mm"
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
include "cplusg.mm"
include "ply1plusg.mm"
include "oveqdr.mm"
include "grpidpropd.mm"
include "trud.mm"
include "eqtri.mm"

theorem ply1mpl0
  let cP: class P
  let cR: class R
  let cM: class M
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume ply1mpl0.m: |- M = ( 1o mPoly R )
  assume ply1mpl0.p: |- P = ( Poly1 ` R )
  assume ply1mpl0.z: |- .0. = ( 0g ` P )


  assert |- .0. = ( 0g ` M )

  proof
    c.0
    cP
    c0g
    cfv
    #
    cM
    c0g
    cfv
    #
    ply1mpl0.z
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
    ply1mpl0.p
    @5
    eqid
    @2
    eqid
    ply1bas
    cM
    @4
    cbs
    ply1mpl0.m
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
    cplusg
    cfv
    #
    cM
    cplusg
    cfv
    #
    @6
    @7
    wceq
    wtru
    @6
    cR
    cM
    cP
    ply1mpl0.p
    ply1mpl0.m
    @6
    eqid
    ply1plusg
    a1i
    oveqdr
    grpidpropd
    trud
    eqtri
end
