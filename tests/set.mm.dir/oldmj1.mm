include "col.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "oldmm4.mm"
include "fveq2d.mm"
include "cops.mm"
include "wceq.mm"
include "olop.mm"
include "3ad2ant1.mm"
include "clat.mm"
include "ollat.mm"
include "opoccl.mm"
include "sylan.mm"
include "3adant3.mm"
include "3adant2.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "opococ.mm"
include "syl2anc.mm"
include "eqtr3d.mm"

theorem oldmj1
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


  assert |- ( ( K e. OL /\ X e. B /\ Y e. B ) -> ( ._|_ ` ( X .\/ Y ) ) = ( ( ._|_ ` X ) ./\ ( ._|_ ` Y ) ) )

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
    c.pe
    cfv
    #
    c.an
    co
    #
    c.pe
    cfv
    #
    c.pe
    cfv
    #
    cX
    cY
    c.or
    co
    #
    c.pe
    cfv
    @6
    @3
    @7
    @9
    c.pe
    cB
    c.or
    cK
    c.an
    c.pe
    cX
    cY
    oldmm1.b
    oldmm1.j
    oldmm1.m
    oldmm1.o
    oldmm4
    fveq2d
    @3
    cK
    cops
    wcel
    #
    @6
    cB
    wcel
    #
    @8
    @6
    wceq
    @0
    @1
    @10
    @2
    cK
    olop
    #
    3ad2ant1
    @3
    cK
    clat
    wcel
    #
    @4
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @11
    @0
    @1
    @13
    @2
    cK
    ollat
    3ad2ant1
    @0
    @1
    @14
    @2
    @0
    @10
    @1
    @14
    @12
    cB
    cK
    c.pe
    cX
    oldmm1.b
    oldmm1.o
    opoccl
    sylan
    3adant3
    @0
    @2
    @15
    @1
    @0
    @10
    @2
    @15
    @12
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
    cK
    c.an
    @4
    @5
    oldmm1.b
    oldmm1.m
    latmcl
    syl3anc
    cB
    cK
    c.pe
    @6
    oldmm1.b
    oldmm1.o
    opococ
    syl2anc
    eqtr3d
end
