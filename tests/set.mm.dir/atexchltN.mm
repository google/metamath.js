include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "ccvr.mm"
include "cfv.mm"
include "wbr.mm"
include "eqid.mm"
include "atexchcvrN.mm"
include "wb.mm"
include "atltcvr.mm"
include "3adant3.mm"
include "wa.mm"
include "simpl.mm"
include "simpr2.mm"
include "simpr1.mm"
include "simpr3.mm"
include "syl13anc.mm"
include "3imtr4d.mm"

theorem atexchltN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.lt: class .<
  let c.or: class .\/
  let cK: class K
  assume atexchlt.s: |- .< = ( lt ` K )
  assume atexchlt.j: |- .\/ = ( join ` K )
  assume atexchlt.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ P =/= R ) -> ( P .< ( Q .\/ R ) -> Q .< ( P .\/ R ) ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cP
    cR
    wne
    #
    w3a
    cP
    cQ
    cR
    c.or
    co
    #
    cK
    ccvr
    cfv
    #
    wbr
    #
    cQ
    cP
    cR
    c.or
    co
    #
    @7
    wbr
    #
    cP
    @6
    c.lt
    wbr
    #
    cQ
    @9
    c.lt
    wbr
    #
    cA
    @7
    cP
    cQ
    cR
    c.or
    cK
    atexchlt.j
    atexchlt.a
    @7
    eqid
    #
    atexchcvrN
    @0
    @4
    @11
    @8
    wb
    @5
    cA
    @7
    cP
    cQ
    cR
    c.lt
    c.or
    cK
    atexchlt.s
    atexchlt.j
    atexchlt.a
    @13
    atltcvr
    3adant3
    @0
    @4
    @12
    @10
    wb
    #
    @5
    @0
    @4
    wa
    @0
    @2
    @1
    @3
    @14
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
    @0
    @1
    @2
    @3
    simpr3
    cA
    @7
    cQ
    cP
    cR
    c.lt
    c.or
    cK
    atexchlt.s
    atexchlt.j
    atexchlt.a
    @13
    atltcvr
    syl13anc
    3adant3
    3imtr4d
end
