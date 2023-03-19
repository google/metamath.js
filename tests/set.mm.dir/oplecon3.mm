include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "wbr.mm"
include "wi.mm"
include "cjn.mm"
include "co.mm"
include "cp1.mm"
include "cmee.mm"
include "cp0.mm"
include "eqid.mm"
include "oposlem.mm"
include "simp1d.mm"
include "simp3d.mm"

theorem oplecon3
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume opcon3.b: |- B = ( Base ` K )
  assume opcon3.l: |- .<_ = ( le ` K )
  assume opcon3.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( X .<_ Y -> ( ._|_ ` Y ) .<_ ( ._|_ ` X ) ) )

  proof
    cK
    cops
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    w3a
    #
    cX
    c.pe
    cfv
    #
    cB
    wcel
    #
    @1
    c.pe
    cfv
    cX
    wceq
    #
    cX
    cY
    c.le
    wbr
    cY
    c.pe
    cfv
    @1
    c.le
    wbr
    wi
    #
    @0
    @2
    @3
    @4
    w3a
    cX
    @1
    cK
    cjn
    cfv
    #
    co
    cK
    cp1
    cfv
    #
    wceq
    cX
    @1
    cK
    cmee
    cfv
    #
    co
    cK
    cp0
    cfv
    #
    wceq
    cB
    @6
    @5
    cK
    c.le
    @7
    c.pe
    cX
    cY
    @8
    opcon3.b
    opcon3.l
    opcon3.o
    @5
    eqid
    @7
    eqid
    @8
    eqid
    @6
    eqid
    oposlem
    simp1d
    simp3d
end
