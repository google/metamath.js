include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wa.mm"
include "cmee.mm"
include "cfv.mm"
include "cp0.mm"
include "wceq.mm"
include "simp3l.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "simp23.mm"
include "eqid.mm"
include "atnem0.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "cbs.mm"
include "simp1.mm"
include "atbase.mm"
include "syl.mm"
include "cvrp.mm"
include "simp3r.mm"
include "hlatexchb2.mm"
include "3adant3r.mm"
include "breqtrd.mm"

theorem atcvrj1
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume atcvrj1x.l: |- .<_ = ( le ` K )
  assume atcvrj1x.j: |- .\/ = ( join ` K )
  assume atcvrj1x.c: |- C = ( <o ` K )
  assume atcvrj1x.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P =/= R /\ P .<_ ( Q .\/ R ) ) ) -> P C ( Q .\/ R ) )

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
    cP
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cP
    cP
    cR
    c.or
    co
    #
    @6
    cC
    @9
    cP
    cR
    cK
    cmee
    cfv
    #
    co
    cK
    cp0
    cfv
    #
    wceq
    #
    cP
    @10
    cC
    wbr
    #
    @9
    @5
    @13
    @0
    @4
    @5
    @7
    simp3l
    @9
    cK
    cal
    wcel
    #
    @1
    @3
    @5
    @13
    wb
    @0
    @4
    @15
    @8
    cK
    hlatl
    3ad2ant1
    @0
    @1
    @2
    @3
    @8
    simp21
    #
    @0
    @1
    @2
    @3
    @8
    simp23
    #
    cA
    cP
    cR
    cK
    @11
    @12
    @11
    eqid
    #
    @12
    eqid
    #
    atcvrj1x.a
    atnem0
    syl3anc
    mpbid
    @9
    @0
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @3
    @13
    @14
    wb
    @0
    @4
    @8
    simp1
    @9
    @1
    @21
    @16
    cA
    @20
    cP
    cK
    @20
    eqid
    #
    atcvrj1x.a
    atbase
    syl
    @17
    cA
    @20
    cC
    cR
    c.or
    cK
    @11
    cP
    @12
    @22
    atcvrj1x.j
    @18
    @19
    atcvrj1x.c
    atcvrj1x.a
    cvrp
    syl3anc
    mpbid
    @9
    @7
    @10
    @6
    wceq
    #
    @0
    @4
    @5
    @7
    simp3r
    @0
    @4
    @5
    @7
    @23
    wb
    @7
    cA
    cP
    cQ
    cR
    c.or
    cK
    c.le
    atcvrj1x.l
    atcvrj1x.j
    atcvrj1x.a
    hlatexchb2
    3adant3r
    mpbid
    breqtrd
end
