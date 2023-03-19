include "cur.mm"
include "cfv.mm"
include "wceq.mm"
include "wtru.mm"
include "cbs.mm"
include "eqid.mm"
include "a1i.mm"
include "zlmbas.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cmulr.mm"
include "zlmmulr.mm"
include "oveqd.mm"
include "rngidpropd.mm"
include "trud.mm"
include "eqtri.mm"

theorem zlm1
  let c.1: class .1.
  let cG: class G
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume zlmlem2.1: |- W = ( ZMod ` G )
  assume zlm1.1: |- .1. = ( 1r ` G )


  assert |- .1. = ( 1r ` W )

  proof
    c.1
    cG
    cur
    cfv
    #
    cW
    cur
    cfv
    #
    zlm1.1
    @0
    @1
    wceq
    wtru
    vx
    vy
    cG
    cbs
    cfv
    #
    cG
    cW
    @2
    @2
    wceq
    wtru
    @2
    eqid
    #
    a1i
    @2
    cW
    cbs
    cfv
    wceq
    wtru
    @2
    cG
    cW
    zlmlem2.1
    @3
    zlmbas
    a1i
    wtru
    vx
    cv
    #
    @2
    wcel
    vy
    cv
    #
    @2
    wcel
    wa
    wa
    #
    cG
    cmulr
    cfv
    #
    cW
    cmulr
    cfv
    #
    @4
    @5
    @7
    @8
    wceq
    @6
    @7
    cG
    cW
    zlmlem2.1
    @7
    eqid
    zlmmulr
    a1i
    oveqd
    rngidpropd
    trud
    eqtri
end
