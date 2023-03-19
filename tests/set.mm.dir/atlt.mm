include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "ccvr.mm"
include "cfv.mm"
include "wne.mm"
include "wb.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "atltcvr.mm"
include "syl13anc.mm"
include "atcvr1.mm"
include "bitr4d.mm"

theorem atlt
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.lt: class .<
  let c.or: class .\/
  let cK: class K
  assume atlt.s: |- .< = ( lt ` K )
  assume atlt.j: |- .\/ = ( join ` K )
  assume atlt.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ P e. A /\ Q e. A ) -> ( P .< ( P .\/ Q ) <-> P =/= Q ) )

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
    w3a
    #
    cP
    cP
    cQ
    c.or
    co
    #
    c.lt
    wbr
    #
    cP
    @4
    cK
    ccvr
    cfv
    #
    wbr
    #
    cP
    cQ
    wne
    @3
    @0
    @1
    @1
    @2
    @5
    @7
    wb
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    #
    @8
    @0
    @1
    @2
    simp3
    cA
    @6
    cP
    cP
    cQ
    c.lt
    c.or
    cK
    atlt.s
    atlt.j
    atlt.a
    @6
    eqid
    #
    atltcvr
    syl13anc
    cA
    @6
    cP
    cQ
    c.or
    cK
    atlt.j
    @9
    atlt.a
    atcvr1
    bitr4d
end
