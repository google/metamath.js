include "col.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "cops.mm"
include "olop.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "oldmm1.mm"
include "syld3an3.mm"
include "opococ.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem oldmm3N
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


  assert |- ( ( K e. OL /\ X e. B /\ Y e. B ) -> ( ._|_ ` ( X ./\ ( ._|_ ` Y ) ) ) = ( ( ._|_ ` X ) .\/ Y ) )

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
    cY
    c.pe
    cfv
    #
    c.an
    co
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    @4
    c.pe
    cfv
    #
    c.or
    co
    #
    @6
    cY
    c.or
    co
    @0
    @1
    @2
    @4
    cB
    wcel
    #
    @5
    @8
    wceq
    @3
    cK
    cops
    wcel
    #
    @2
    @9
    @0
    @1
    @10
    @2
    cK
    olop
    3ad2ant1
    #
    @0
    @1
    @2
    simp3
    #
    cB
    cK
    c.pe
    cY
    oldmm1.b
    oldmm1.o
    opoccl
    syl2anc
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
    oldmm1
    syld3an3
    @3
    @7
    cY
    @6
    c.or
    @3
    @10
    @2
    @7
    cY
    wceq
    @11
    @12
    cB
    cK
    c.pe
    cY
    oldmm1.b
    oldmm1.o
    opococ
    syl2anc
    oveq2d
    eqtrd
end
