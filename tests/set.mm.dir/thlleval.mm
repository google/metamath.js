include "cvv.mm"
include "wcel.mm"
include "wbr.mm"
include "wss.mm"
include "wb.mm"
include "ccss.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cipo.mm"
include "eqid.mm"
include "cple.mm"
include "thlle.mm"
include "eqtr4i.mm"
include "ipole.mm"
include "mp3an1.mm"

theorem thlleval
  let cC: class C
  let cS: class S
  let cT: class T
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let cI: class I
  let c.pe: class ._|_
  assume thlval.k: |- K = ( toHL ` W )
  assume thlbas.c: |- C = ( CSubSp ` W )
  assume thlleval.l: |- .<_ = ( le ` K )


  assert |- ( ( S e. C /\ T e. C ) -> ( S .<_ T <-> S C_ T ) )

  proof
    cC
    cvv
    wcel
    cS
    cC
    wcel
    cT
    cC
    wcel
    cS
    cT
    c.le
    wbr
    cS
    cT
    wss
    wb
    cC
    cW
    ccss
    cfv
    cvv
    thlbas.c
    cW
    ccss
    fvex
    eqeltri
    cC
    cC
    cipo
    cfv
    #
    c.le
    cvv
    cS
    cT
    @0
    eqid
    #
    c.le
    cK
    cple
    cfv
    @0
    cple
    cfv
    #
    thlleval.l
    cC
    @0
    cK
    @2
    cW
    thlval.k
    thlbas.c
    @1
    @2
    eqid
    thlle
    eqtr4i
    ipole
    mp3an1
end
