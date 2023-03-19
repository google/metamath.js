include "coml.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "omllaw.mm"
include "eqcom.mm"
include "clat.mm"
include "omllat.mm"
include "3ad2ant1.mm"
include "cops.mm"
include "omlop.mm"
include "opoccl.mm"
include "sylan.mm"
include "3adant3.mm"
include "simp3.mm"
include "latmcom.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "syl5bb.mm"
include "sylibrd.mm"

theorem omllaw2N
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume omllaw.b: |- B = ( Base ` K )
  assume omllaw.l: |- .<_ = ( le ` K )
  assume omllaw.j: |- .\/ = ( join ` K )
  assume omllaw.m: |- ./\ = ( meet ` K )
  assume omllaw.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OML /\ X e. B /\ Y e. B ) -> ( X .<_ Y -> ( X .\/ ( ( ._|_ ` X ) ./\ Y ) ) = Y ) )

  proof
    cK
    coml
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    cY
    cX
    cY
    cX
    c.pe
    cfv
    #
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    cX
    @4
    cY
    c.an
    co
    #
    c.or
    co
    #
    cY
    wceq
    #
    cB
    c.or
    cK
    c.le
    c.an
    c.pe
    cX
    cY
    omllaw.b
    omllaw.l
    omllaw.j
    omllaw.m
    omllaw.o
    omllaw
    @10
    cY
    @9
    wceq
    @3
    @7
    @9
    cY
    eqcom
    @3
    @9
    @6
    cY
    @3
    @8
    @5
    cX
    c.or
    @3
    cK
    clat
    wcel
    #
    @4
    cB
    wcel
    #
    @2
    @8
    @5
    wceq
    @0
    @1
    @11
    @2
    cK
    omllat
    3ad2ant1
    @0
    @1
    @12
    @2
    @0
    cK
    cops
    wcel
    @1
    @12
    cK
    omlop
    cB
    cK
    c.pe
    cX
    omllaw.b
    omllaw.o
    opoccl
    sylan
    3adant3
    @0
    @1
    @2
    simp3
    cB
    cK
    c.an
    @4
    cY
    omllaw.b
    omllaw.m
    latmcom
    syl3anc
    oveq2d
    eqeq2d
    syl5bb
    sylibrd
end
