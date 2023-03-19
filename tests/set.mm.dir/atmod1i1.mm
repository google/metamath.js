include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cpmap.mm"
include "cfv.mm"
include "cpadd.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr1.mm"
include "eqid.mm"
include "pmapjat2.mm"
include "syl3anc.mm"
include "wi.mm"
include "atbase.mm"
include "hlmod1i.mm"
include "syl3anr1.mm"
include "mpan2d.mm"
include "3impia.mm"
include "eqcomd.mm"

theorem atmod1i1
  let cA: class A
  let cB: class B
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  assume atmod.b: |- B = ( Base ` K )
  assume atmod.l: |- .<_ = ( le ` K )
  assume atmod.j: |- .\/ = ( join ` K )
  assume atmod.m: |- ./\ = ( meet ` K )
  assume atmod.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ X e. B /\ Y e. B ) /\ P .<_ Y ) -> ( P .\/ ( X ./\ Y ) ) = ( ( P .\/ X ) ./\ Y ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
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
    cP
    cY
    c.le
    wbr
    #
    w3a
    cP
    cX
    c.or
    co
    #
    cY
    c.an
    co
    #
    cP
    cX
    cY
    c.an
    co
    c.or
    co
    #
    @0
    @4
    @5
    @7
    @8
    wceq
    #
    @0
    @4
    wa
    #
    @5
    @6
    cK
    cpmap
    cfv
    #
    cfv
    cP
    @11
    cfv
    cX
    @11
    cfv
    cK
    cpadd
    cfv
    #
    co
    wceq
    #
    @9
    @10
    @0
    @2
    @1
    @13
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr1
    cA
    cB
    @12
    cP
    c.or
    cK
    @11
    cX
    atmod.b
    atmod.j
    atmod.a
    @11
    eqid
    #
    @12
    eqid
    #
    pmapjat2
    syl3anc
    @1
    cP
    cB
    wcel
    @0
    @2
    @3
    @5
    @13
    wa
    @9
    wi
    cA
    cB
    cP
    cK
    atmod.b
    atmod.a
    atbase
    cB
    @12
    @11
    c.or
    cK
    c.le
    c.an
    cP
    cX
    cY
    atmod.b
    atmod.l
    atmod.j
    atmod.m
    @14
    @15
    hlmod1i
    syl3anr1
    mpan2d
    3impia
    eqcomd
end
