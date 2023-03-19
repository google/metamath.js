include "c0g.mm"
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
include "cplusg.mm"
include "zlmplusg.mm"
include "oveqd.mm"
include "grpidpropd.mm"
include "trud.mm"
include "eqtri.mm"

theorem zlm0
  let cG: class G
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume zlmlem2.1: |- W = ( ZMod ` G )
  assume zlm0.1: |- .0. = ( 0g ` G )


  assert |- .0. = ( 0g ` W )

  proof
    c.0
    cG
    c0g
    cfv
    #
    cW
    c0g
    cfv
    #
    zlm0.1
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
    cplusg
    cfv
    #
    cW
    cplusg
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
    zlmplusg
    a1i
    oveqd
    grpidpropd
    trud
    eqtri
end
