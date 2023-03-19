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
include "3adant3.mm"
include "oldmm1.mm"
include "syld3an2.mm"
include "opococ.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem oldmm2
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


  assert |- ( ( K e. OL /\ X e. B /\ Y e. B ) -> ( ._|_ ` ( ( ._|_ ` X ) ./\ Y ) ) = ( X .\/ ( ._|_ ` Y ) ) )

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
    #
    cY
    c.an
    co
    c.pe
    cfv
    #
    @4
    c.pe
    cfv
    #
    cY
    c.pe
    cfv
    #
    c.or
    co
    #
    cX
    @7
    c.or
    co
    @0
    @4
    cB
    wcel
    #
    @1
    @2
    @5
    @8
    wceq
    @0
    @1
    @9
    @2
    @0
    cK
    cops
    wcel
    #
    @1
    @9
    cK
    olop
    #
    cB
    cK
    c.pe
    cX
    oldmm1.b
    oldmm1.o
    opoccl
    sylan
    3adant3
    cB
    c.or
    cK
    c.an
    c.pe
    @4
    cY
    oldmm1.b
    oldmm1.j
    oldmm1.m
    oldmm1.o
    oldmm1
    syld3an2
    @3
    @6
    cX
    @7
    c.or
    @0
    @1
    @6
    cX
    wceq
    #
    @2
    @0
    @10
    @1
    @12
    @11
    cB
    cK
    c.pe
    cX
    oldmm1.b
    oldmm1.o
    opococ
    sylan
    3adant3
    oveq1d
    eqtrd
end
