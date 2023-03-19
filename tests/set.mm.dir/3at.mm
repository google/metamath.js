include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "3atlem7.mm"
include "3expia.mm"
include "wi.mm"
include "clat.mm"
include "hllat.mm"
include "cbs.mm"
include "cfv.mm"
include "simpl.mm"
include "simpr1.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simpr2.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simpr3.mm"
include "latref.mm"
include "syldan.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "sylan.mm"
include "3adant3.mm"
include "adantr.mm"
include "impbid.mm"

theorem 3at
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  assume 3at.l: |- .<_ = ( le ` K )
  assume 3at.j: |- .\/ = ( join ` K )
  assume 3at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( S e. A /\ T e. A /\ U e. A ) ) /\ ( -. R .<_ ( P .\/ Q ) /\ P =/= Q ) ) -> ( ( ( P .\/ Q ) .\/ R ) .<_ ( ( S .\/ T ) .\/ U ) <-> ( ( P .\/ Q ) .\/ R ) = ( ( S .\/ T ) .\/ U ) ) )

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
    cS
    cA
    wcel
    cT
    cA
    wcel
    cU
    cA
    wcel
    w3a
    #
    w3a
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    cP
    cQ
    wne
    wa
    #
    wa
    @7
    cR
    c.or
    co
    #
    cS
    cT
    c.or
    co
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    @9
    @10
    wceq
    #
    @6
    @8
    @11
    @12
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    c.or
    cK
    c.le
    3at.l
    3at.j
    3at.a
    3atlem7
    3expia
    @6
    @12
    @11
    wi
    #
    @8
    @0
    @4
    @13
    @5
    @0
    cK
    clat
    wcel
    #
    @4
    @13
    cK
    hllat
    @14
    @4
    wa
    #
    @9
    @9
    c.le
    wbr
    #
    @12
    @11
    @14
    @4
    @9
    cK
    cbs
    cfv
    #
    wcel
    #
    @16
    @15
    @14
    @7
    @17
    wcel
    #
    cR
    @17
    wcel
    #
    @18
    @14
    @4
    simpl
    #
    @15
    @14
    cP
    @17
    wcel
    #
    cQ
    @17
    wcel
    #
    @19
    @21
    @15
    @1
    @22
    @14
    @1
    @2
    @3
    simpr1
    cA
    @17
    cP
    cK
    @17
    eqid
    #
    3at.a
    atbase
    syl
    @15
    @2
    @23
    @14
    @1
    @2
    @3
    simpr2
    cA
    @17
    cQ
    cK
    @24
    3at.a
    atbase
    syl
    @17
    c.or
    cK
    cP
    cQ
    @24
    3at.j
    latjcl
    syl3anc
    @15
    @3
    @20
    @14
    @1
    @2
    @3
    simpr3
    cA
    @17
    cR
    cK
    @24
    3at.a
    atbase
    syl
    @17
    c.or
    cK
    @7
    cR
    @24
    3at.j
    latjcl
    syl3anc
    @17
    cK
    c.le
    @9
    @24
    3at.l
    latref
    syldan
    @9
    @10
    @9
    c.le
    breq2
    syl5ibcom
    sylan
    3adant3
    adantr
    impbid
end
