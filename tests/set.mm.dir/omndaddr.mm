include "coppg.mm"
include "cfv.mm"
include "comnd.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cplusg.mm"
include "co.mm"
include "eqid.mm"
include "oppgbas.mm"
include "oppgle.mm"
include "omndadd.mm"
include "oppgplus.mm"
include "3brtr3g.mm"

theorem omndaddr
  let cB: class B
  let c.pl: class .+
  let c.le: class .<_
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume omndadd.0: |- B = ( Base ` M )
  assume omndadd.1: |- .<_ = ( le ` M )
  assume omndadd.2: |- .+ = ( +g ` M )


  assert |- ( ( ( oppG ` M ) e. oMnd /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ X .<_ Y ) -> ( Z .+ X ) .<_ ( Z .+ Y ) )

  proof
    cM
    coppg
    cfv
    #
    comnd
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    cX
    cY
    c.le
    wbr
    w3a
    cX
    cZ
    @0
    cplusg
    cfv
    #
    co
    cY
    cZ
    @1
    co
    cZ
    cX
    c.pl
    co
    cZ
    cY
    c.pl
    co
    c.le
    cB
    @1
    c.le
    @0
    cX
    cY
    cZ
    cB
    cM
    @0
    @0
    eqid
    #
    omndadd.0
    oppgbas
    cM
    c.le
    @0
    @2
    omndadd.1
    oppgle
    @1
    eqid
    #
    omndadd
    c.pl
    @1
    cM
    @0
    cX
    cZ
    omndadd.2
    @2
    @3
    oppgplus
    c.pl
    @1
    cM
    @0
    cY
    cZ
    omndadd.2
    @2
    @3
    oppgplus
    3brtr3g
end
