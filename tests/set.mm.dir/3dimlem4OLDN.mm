include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simp2l.mm"
include "simp2r.mm"
include "wi.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp3l.mm"
include "necomd.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "sylibrd.mm"
include "3ad2ant1.mm"
include "mtod.mm"
include "simp3.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "latjrot.mm"
include "syl13anc.mm"
include "hlatjcl.mm"
include "simp3r.mm"
include "hlexch1.mm"
include "sylbird.mm"
include "3jca.mm"

theorem 3dimlem4OLDN
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


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( Q =/= R /\ -. S .<_ ( Q .\/ R ) ) ) /\ ( P =/= Q /\ -. P .<_ ( Q .\/ R ) ) /\ -. P .<_ ( ( Q .\/ R ) .\/ S ) ) -> ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) )

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
    cQ
    cR
    wne
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
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cP
    @8
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cP
    @8
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
    @12
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    cS
    @19
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @11
    @12
    @14
    @17
    simp2l
    @18
    @20
    @13
    @11
    @12
    @14
    @17
    simp2r
    @11
    @15
    @20
    @13
    wi
    @17
    @11
    @20
    cP
    cR
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @13
    @11
    @0
    @4
    @1
    @2
    cR
    cQ
    wne
    @20
    @24
    wi
    @0
    @1
    @2
    @6
    @10
    simp11
    #
    @3
    @4
    @5
    @10
    simp2l
    #
    @0
    @1
    @2
    @6
    @10
    simp12
    #
    @0
    @1
    @2
    @6
    @10
    simp13
    #
    @11
    cQ
    cR
    @3
    @6
    @7
    @9
    simp3l
    necomd
    cA
    cR
    cP
    cQ
    c.or
    cK
    c.le
    3dim0.l
    3dim0.j
    3dim0.a
    hlatexch2
    syl131anc
    @11
    @8
    @23
    cP
    c.le
    @11
    @0
    @2
    @4
    @8
    @23
    wceq
    @25
    @28
    @26
    cA
    c.or
    cK
    cQ
    cR
    3dim0.j
    3dim0.a
    hlatjcom
    syl3anc
    breq2d
    sylibrd
    3ad2ant1
    mtod
    @18
    @22
    @16
    @11
    @15
    @17
    simp3
    @11
    @15
    @22
    @16
    wi
    @17
    @11
    @22
    cS
    @8
    cP
    c.or
    co
    #
    c.le
    wbr
    #
    @16
    @11
    @29
    @21
    cS
    c.le
    @11
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
    @32
    wcel
    #
    cP
    @32
    wcel
    #
    @29
    @21
    wceq
    @11
    @0
    @31
    @25
    cK
    hllat
    syl
    @11
    @2
    @33
    @28
    cA
    @32
    cQ
    cK
    @32
    eqid
    #
    3dim0.a
    atbase
    syl
    @11
    @4
    @34
    @26
    cA
    @32
    cR
    cK
    @36
    3dim0.a
    atbase
    syl
    @11
    @1
    @35
    @27
    cA
    @32
    cP
    cK
    @36
    3dim0.a
    atbase
    syl
    @32
    c.or
    cK
    cQ
    cR
    cP
    @36
    3dim0.j
    latjrot
    syl13anc
    breq2d
    @11
    @0
    @5
    @1
    @8
    @32
    wcel
    #
    @9
    @30
    @16
    wi
    @25
    @3
    @4
    @5
    @10
    simp2r
    @27
    @11
    @0
    @2
    @4
    @37
    @25
    @28
    @26
    cA
    @32
    c.or
    cK
    cQ
    cR
    @36
    3dim0.j
    3dim0.a
    hlatjcl
    syl3anc
    @3
    @6
    @7
    @9
    simp3r
    cA
    @32
    cS
    cP
    c.or
    cK
    c.le
    @8
    @36
    3dim0.l
    3dim0.j
    3dim0.a
    hlexch1
    syl131anc
    sylbird
    3ad2ant1
    mtod
    3jca
end
