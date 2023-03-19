include "col.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cops.mm"
include "olop.mm"
include "opoccl.mm"
include "sylan.mm"
include "3adant2.mm"
include "oldmj2.mm"
include "syld3an3.mm"
include "opococ.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem oldmj4
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  assume oldmm1.b: |- B = ( Base ` K )
  assume oldmm1.j: |- .\/ = ( join ` K )
  assume oldmm1.m: |- ./\ = ( meet ` K )
  assume oldmm1.o: |- ._|_ = ( oc ` K )


  assert |- ( ( K e. OL /\ X e. B /\ Y e. B ) -> ( ._|_ ` ( ( ._|_ ` X ) .\/ ( ._|_ ` Y ) ) ) = ( X ./\ Y ) )

  proof
    cK
    col
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
    c.pe
    cfv
    cY
    c.pe
    cfv
    #
    c.or
    co
    c.pe
    cfv
    #
    cX
    @4
    c.pe
    cfv
    #
    c.an
    co
    #
    cX
    cY
    c.an
    co
    @0
    @1
    @2
    @4
    cB
    wcel
    #
    @5
    @7
    wceq
    @0
    @2
    @8
    @1
    @0
    cK
    cops
    wcel
    #
    @2
    @8
    cK
    olop
    #
    cB
    cK
    c.pe
    cY
    oldmm1.b
    oldmm1.o
    opoccl
    sylan
    3adant2
    cB
    c.or
    cK
    c.an
    c.pe
    cX
    @4
    oldmm1.b
    oldmm1.j
    oldmm1.m
    oldmm1.o
    oldmj2
    syld3an3
    @3
    @6
    cY
    cX
    c.an
    @0
    @2
    @6
    cY
    wceq
    #
    @1
    @0
    @9
    @2
    @11
    @10
    cB
    cK
    c.pe
    cY
    oldmm1.b
    oldmm1.o
    opococ
    sylan
    3adant2
    oveq2d
    eqtrd
end
