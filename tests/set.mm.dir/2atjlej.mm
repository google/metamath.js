include "chlt.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "simp33.mm"
include "wb.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp31.mm"
include "simp32.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"
include "lnnat.mm"
include "syl3anc.mm"
include "eqneltrrd.mm"
include "mpbird.mm"

theorem 2atjlej
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vu: setvar u
  let cT: class T
  assume ps1.l: |- .<_ = ( le ` K )
  assume ps1.j: |- .\/ = ( join ` K )
  assume ps1.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ P =/= Q ) /\ ( R e. A /\ S e. A /\ ( P .\/ Q ) .<_ ( R .\/ S ) ) ) -> R =/= S )

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
    cP
    cQ
    wne
    #
    w3a
    #
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cP
    cQ
    c.or
    co
    #
    cR
    cS
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cR
    cS
    wne
    #
    @8
    cA
    wcel
    wn
    #
    @11
    @7
    @8
    cA
    @11
    @9
    @7
    @8
    wceq
    #
    @0
    @4
    @5
    @6
    @9
    simp33
    @11
    @0
    @1
    @2
    @3
    @5
    @6
    @9
    @14
    wb
    @0
    @4
    @10
    simp1
    #
    @0
    @1
    @2
    @3
    @10
    simp21
    #
    @0
    @1
    @2
    @3
    @10
    simp22
    #
    @0
    @1
    @2
    @3
    @10
    simp23
    #
    @0
    @4
    @5
    @6
    @9
    simp31
    #
    @0
    @4
    @5
    @6
    @9
    simp32
    #
    cA
    cP
    cQ
    cR
    cS
    c.or
    cK
    c.le
    ps1.l
    ps1.j
    ps1.a
    ps-1
    syl132anc
    mpbid
    @11
    @3
    @7
    cA
    wcel
    wn
    #
    @18
    @11
    @0
    @1
    @2
    @3
    @21
    wb
    @15
    @16
    @17
    cA
    cP
    cQ
    c.or
    cK
    ps1.j
    ps1.a
    lnnat
    syl3anc
    mpbid
    eqneltrrd
    @11
    @0
    @5
    @6
    @12
    @13
    wb
    @15
    @19
    @20
    cA
    cR
    cS
    c.or
    cK
    ps1.j
    ps1.a
    lnnat
    syl3anc
    mpbird
end
