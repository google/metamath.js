include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simp33.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11.mm"
include "hllat.mm"
include "syl.mm"
include "simp13.mm"
include "eqid.mm"
include "atbase.mm"
include "simp2l.mm"
include "simp12.mm"
include "latjrot.mm"
include "syl13anc.mm"
include "breq2d.mm"
include "wi.mm"
include "simp2r.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp31.mm"
include "hlexch1.mm"
include "syl131anc.mm"
include "sylbird.mm"
include "mtod.mm"

theorem 3dimlem4a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vs: setvar s
  assume 3dim0.j: |- .\/ = ( join ` K )
  assume 3dim0.l: |- .<_ = ( le ` K )
  assume 3dim0.a: |- A = ( Atoms ` K )


  assert |- ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( -. S .<_ ( Q .\/ R ) /\ -. P .<_ ( Q .\/ R ) /\ -. P .<_ ( ( Q .\/ R ) .\/ S ) ) ) -> -. S .<_ ( ( P .\/ Q ) .\/ R ) )

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
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    wa
    #
    cS
    cQ
    cR
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cP
    @7
    c.le
    wbr
    wn
    #
    cP
    @7
    cS
    c.or
    co
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    w3a
    #
    cS
    cP
    cQ
    c.or
    co
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    @10
    @3
    @6
    @8
    @9
    @11
    simp33
    @13
    @15
    cS
    @7
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    @10
    @13
    @16
    @14
    cS
    c.le
    @13
    cK
    clat
    wcel
    #
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @19
    wcel
    #
    cP
    @19
    wcel
    #
    @16
    @14
    wceq
    @13
    @0
    @18
    @0
    @1
    @2
    @6
    @12
    simp11
    #
    cK
    hllat
    syl
    #
    @13
    @2
    @20
    @0
    @1
    @2
    @6
    @12
    simp13
    cA
    @19
    cQ
    cK
    @19
    eqid
    #
    3dim0.a
    atbase
    syl
    #
    @13
    @4
    @21
    @3
    @4
    @5
    @12
    simp2l
    cA
    @19
    cR
    cK
    @25
    3dim0.a
    atbase
    syl
    #
    @13
    @1
    @22
    @0
    @1
    @2
    @6
    @12
    simp12
    #
    cA
    @19
    cP
    cK
    @25
    3dim0.a
    atbase
    syl
    @19
    c.or
    cK
    cQ
    cR
    cP
    @25
    3dim0.j
    latjrot
    syl13anc
    breq2d
    @13
    @0
    @5
    @1
    @7
    @19
    wcel
    #
    @8
    @17
    @10
    wi
    @23
    @3
    @4
    @5
    @12
    simp2r
    @28
    @13
    @18
    @20
    @21
    @29
    @24
    @26
    @27
    @19
    c.or
    cK
    cQ
    cR
    @25
    3dim0.j
    latjcl
    syl3anc
    @3
    @6
    @8
    @9
    @11
    simp31
    cA
    @19
    cS
    cP
    c.or
    cK
    c.le
    @7
    @25
    3dim0.l
    3dim0.j
    3dim0.a
    hlexch1
    syl131anc
    sylbird
    mtod
end
