include "wss.mm"
include "cfv.mm"
include "cbs.mm"
include "cv.mm"
include "wcel.mm"
include "cip.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "sstr2.mm"
include "idd.mm"
include "ssralv.mm"
include "3anim123d.mm"
include "eqid.mm"
include "elocv.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem ocv2ss
  let cS: class S
  let cT: class T
  let c.pe: class ._|_
  let cW: class W
  let cL: class L
  let vx: setvar x
  let vy: setvar y
  let c.0: class .0.
  assume ocv2ss.o: |- ._|_ = ( ocv ` W )


  assert |- ( T C_ S -> ( ._|_ ` S ) C_ ( ._|_ ` T ) )

  proof
    cT
    cS
    wss
    #
    vx
    cS
    c.pe
    cfv
    #
    cT
    c.pe
    cfv
    #
    @0
    cS
    cW
    cbs
    cfv
    #
    wss
    #
    vx
    cv
    #
    @3
    wcel
    #
    @5
    vy
    cv
    cW
    cip
    cfv
    #
    co
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    vy
    cS
    wral
    #
    w3a
    cT
    @3
    wss
    #
    @6
    @10
    vy
    cT
    wral
    #
    w3a
    @5
    @1
    wcel
    @5
    @2
    wcel
    @0
    @4
    @12
    @6
    @6
    @11
    @13
    cT
    cS
    @3
    sstr2
    @0
    @6
    idd
    @10
    vy
    cT
    cS
    ssralv
    3anim123d
    vy
    @5
    cS
    @8
    @7
    c.pe
    @3
    cW
    @9
    @3
    eqid
    #
    @7
    eqid
    #
    @8
    eqid
    #
    @9
    eqid
    #
    ocv2ss.o
    elocv
    vy
    @5
    cT
    @8
    @7
    c.pe
    @3
    cW
    @9
    @14
    @15
    @16
    @17
    ocv2ss.o
    elocv
    3imtr4g
    ssrdv
end
