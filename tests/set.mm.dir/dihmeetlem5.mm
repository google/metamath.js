include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simprl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simprr.mm"
include "atmod2i1.mm"
include "syl131anc.mm"
include "eqcomd.mm"

theorem dihmeetlem5
  let cA: class A
  let cB: class B
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume dihmeetlem5.b: |- B = ( Base ` K )
  assume dihmeetlem5.l: |- .<_ = ( le ` K )
  assume dihmeetlem5.j: |- .\/ = ( join ` K )
  assume dihmeetlem5.m: |- ./\ = ( meet ` K )
  assume dihmeetlem5.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ ( Q e. A /\ Q .<_ X ) ) -> ( X ./\ ( Y .\/ Q ) ) = ( ( X ./\ Y ) .\/ Q ) )

  proof
    cK
    chlt
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
    cQ
    cA
    wcel
    #
    cQ
    cX
    c.le
    wbr
    #
    wa
    #
    wa
    #
    cX
    cY
    c.an
    co
    cQ
    c.or
    co
    #
    cX
    cY
    cQ
    c.or
    co
    c.an
    co
    #
    @7
    @0
    @4
    @1
    @2
    @5
    @8
    @9
    wceq
    @0
    @1
    @2
    @6
    simpl1
    @3
    @4
    @5
    simprl
    @0
    @1
    @2
    @6
    simpl2
    @0
    @1
    @2
    @6
    simpl3
    @3
    @4
    @5
    simprr
    cA
    cB
    cQ
    c.or
    cK
    c.le
    c.an
    cX
    cY
    dihmeetlem5.b
    dihmeetlem5.l
    dihmeetlem5.j
    dihmeetlem5.m
    dihmeetlem5.a
    atmod2i1
    syl131anc
    eqcomd
end
