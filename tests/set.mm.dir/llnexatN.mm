include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "ccvr.mm"
include "cfv.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "3jca.mm"
include "eqid.mm"
include "atcvrlln2.mm"
include "sylan.mm"
include "wn.mm"
include "cbs.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl3.mm"
include "atbase.mm"
include "syl.mm"
include "simpl2.mm"
include "llnbase.mm"
include "cvrval3.mm"
include "syl3anc.mm"
include "cal.mm"
include "simpll1.mm"
include "hlatl.mm"
include "simpr.mm"
include "simpll3.mm"
include "atncmp.mm"
include "anbi1d.mm"
include "necom.mm"
include "eqcom.mm"
include "anbi12i.mm"
include "syl6bb.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem llnexatN
  let cA: class A
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cX: class X
  let vq: setvar q
  assume llnexat.l: |- .<_ = ( le ` K )
  assume llnexat.j: |- .\/ = ( join ` K )
  assume llnexat.a: |- A = ( Atoms ` K )
  assume llnexat.n: |- N = ( LLines ` K )

  disjoint A q
  disjoint K q
  disjoint .<_ q
  disjoint N q
  disjoint P q
  disjoint X q
  assert |- ( ( ( K e. HL /\ X e. N /\ P e. A ) /\ P .<_ X ) -> E. q e. A ( P =/= q /\ X = ( P .\/ q ) ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cP
    cA
    wcel
    #
    w3a
    #
    cP
    cX
    c.le
    wbr
    #
    wa
    #
    cP
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    cP
    vq
    cv
    #
    wne
    #
    cX
    cP
    @8
    c.or
    co
    #
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    @3
    @0
    @2
    @1
    w3a
    @4
    @7
    @3
    @0
    @2
    @1
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @0
    @1
    @2
    simp2
    3jca
    cA
    @6
    cP
    cK
    c.le
    cN
    cX
    llnexat.l
    @6
    eqid
    #
    llnexat.a
    llnexat.n
    atcvrlln2
    sylan
    @5
    @7
    @8
    cP
    c.le
    wbr
    wn
    #
    @10
    cX
    wceq
    #
    wa
    #
    vq
    cA
    wrex
    #
    @13
    @5
    @0
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    cX
    @19
    wcel
    #
    @7
    @18
    wb
    @0
    @1
    @2
    @4
    simpl1
    @5
    @2
    @20
    @0
    @1
    @2
    @4
    simpl3
    cA
    @19
    cP
    cK
    @19
    eqid
    #
    llnexat.a
    atbase
    syl
    @5
    @1
    @21
    @0
    @1
    @2
    @4
    simpl2
    @19
    cK
    cN
    cX
    @22
    llnexat.n
    llnbase
    syl
    cA
    @19
    @6
    c.or
    cK
    c.le
    cP
    cX
    vq
    @22
    llnexat.l
    llnexat.j
    @14
    llnexat.a
    cvrval3
    syl3anc
    @5
    @17
    @12
    vq
    cA
    @5
    @8
    cA
    wcel
    #
    wa
    #
    @17
    @8
    cP
    wne
    #
    @16
    wa
    @12
    @24
    @15
    @25
    @16
    @24
    cK
    cal
    wcel
    #
    @23
    @2
    @15
    @25
    wb
    @24
    @0
    @26
    @0
    @1
    @2
    @4
    @23
    simpll1
    cK
    hlatl
    syl
    @5
    @23
    simpr
    @0
    @1
    @2
    @4
    @23
    simpll3
    cA
    @8
    cP
    cK
    c.le
    llnexat.l
    llnexat.a
    atncmp
    syl3anc
    anbi1d
    @25
    @9
    @16
    @11
    @8
    cP
    necom
    @10
    cX
    eqcom
    anbi12i
    syl6bb
    rexbidva
    bitrd
    mpbid
end
