include "col.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cple.mm"
include "cfv.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "clat.mm"
include "ollat.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "atbase.mm"
include "syl.mm"
include "eqid.mm"
include "latmle2.mm"
include "syl3anc.mm"
include "cops.mm"
include "wb.mm"
include "olop.mm"
include "latmcl.mm"
include "leatb.mm"
include "mpbid.mm"

theorem meetat
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let c.0: class .0.
  assume m.b: |- B = ( Base ` K )
  assume m.m: |- ./\ = ( meet ` K )
  assume m.z: |- .0. = ( 0. ` K )
  assume m.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. OL /\ X e. B /\ P e. A ) -> ( ( X ./\ P ) = P \/ ( X ./\ P ) = .0. ) )

  proof
    cK
    col
    wcel
    #
    cX
    cB
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cX
    cP
    c.an
    co
    #
    cP
    cK
    cple
    cfv
    #
    wbr
    #
    @4
    cP
    wceq
    @4
    c.0
    wceq
    wo
    #
    @3
    cK
    clat
    wcel
    #
    @1
    cP
    cB
    wcel
    #
    @6
    @0
    @1
    @8
    @2
    cK
    ollat
    3ad2ant1
    #
    @0
    @1
    @2
    simp2
    #
    @3
    @2
    @9
    @0
    @1
    @2
    simp3
    #
    cA
    cB
    cP
    cK
    m.b
    m.a
    atbase
    syl
    #
    cB
    cK
    @5
    c.an
    cX
    cP
    m.b
    @5
    eqid
    #
    m.m
    latmle2
    syl3anc
    @3
    cK
    cops
    wcel
    #
    @4
    cB
    wcel
    #
    @2
    @6
    @7
    wb
    @0
    @1
    @15
    @2
    cK
    olop
    3ad2ant1
    @3
    @8
    @1
    @9
    @16
    @10
    @11
    @13
    cB
    cK
    c.an
    cX
    cP
    m.b
    m.m
    latmcl
    syl3anc
    @12
    cA
    cB
    cP
    cK
    @5
    @4
    c.0
    m.b
    @14
    m.z
    m.a
    leatb
    syl3anc
    mpbid
end
