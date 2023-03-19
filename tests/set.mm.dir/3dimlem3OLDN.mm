include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "simpr1.mm"
include "simpr2.mm"
include "wi.mm"
include "simpl11.mm"
include "simpl2l.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl3l.mm"
include "necomd.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "wceq.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "breq2d.mm"
include "sylibrd.mm"
include "mtod.mm"
include "simpl3r.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "latjrot.mm"
include "syl13anc.mm"
include "simpr3.mm"
include "wb.mm"
include "simpl2r.mm"
include "hlatjcl.mm"
include "hlexchb1.mm"
include "mpbid.mm"
include "eqtr3d.mm"
include "mtbird.mm"
include "3jca.mm"

theorem 3dimlem3OLDN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
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


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( Q =/= R /\ -. T .<_ ( ( Q .\/ R ) .\/ S ) ) ) /\ ( P =/= Q /\ -. P .<_ ( Q .\/ R ) /\ P .<_ ( ( Q .\/ R ) .\/ S ) ) ) -> ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. T .<_ ( ( P .\/ Q ) .\/ R ) ) )

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
    cT
    cQ
    cR
    c.or
    co
    #
    cS
    c.or
    co
    #
    c.le
    wbr
    #
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
    cP
    @9
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    @14
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
    cT
    @20
    cR
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @13
    @14
    @16
    @17
    simpr1
    @19
    @21
    @15
    @13
    @14
    @16
    @17
    simpr2
    #
    @19
    @21
    cP
    cR
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @15
    @19
    @0
    @4
    @1
    @2
    cR
    cQ
    wne
    @21
    @26
    wi
    @0
    @1
    @2
    @6
    @12
    @18
    simpl11
    #
    @4
    @5
    @3
    @12
    @18
    simpl2l
    #
    @0
    @1
    @2
    @6
    @12
    @18
    simpl12
    #
    @0
    @1
    @2
    @6
    @12
    @18
    simpl13
    #
    @19
    cQ
    cR
    @7
    @11
    @3
    @6
    @18
    simpl3l
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
    @19
    @8
    @25
    cP
    c.le
    @19
    @0
    @2
    @4
    @8
    @25
    wceq
    @27
    @30
    @28
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
    mtod
    @19
    @23
    @10
    @7
    @11
    @3
    @6
    @18
    simpl3r
    @19
    @22
    @9
    cT
    c.le
    @19
    @8
    cP
    c.or
    co
    #
    @22
    @9
    @19
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
    @33
    wcel
    #
    cP
    @33
    wcel
    #
    @31
    @22
    wceq
    @19
    @0
    @32
    @27
    cK
    hllat
    syl
    @19
    @2
    @34
    @30
    cA
    @33
    cQ
    cK
    @33
    eqid
    #
    3dim0.a
    atbase
    syl
    @19
    @4
    @35
    @28
    cA
    @33
    cR
    cK
    @37
    3dim0.a
    atbase
    syl
    @19
    @1
    @36
    @29
    cA
    @33
    cP
    cK
    @37
    3dim0.a
    atbase
    syl
    @33
    c.or
    cK
    cQ
    cR
    cP
    @37
    3dim0.j
    latjrot
    syl13anc
    @19
    @17
    @31
    @9
    wceq
    #
    @13
    @14
    @16
    @17
    simpr3
    @19
    @0
    @1
    @5
    @8
    @33
    wcel
    #
    @16
    @17
    @38
    wb
    @27
    @29
    @4
    @5
    @3
    @12
    @18
    simpl2r
    @19
    @0
    @2
    @4
    @39
    @27
    @30
    @28
    cA
    @33
    c.or
    cK
    cQ
    cR
    @37
    3dim0.j
    3dim0.a
    hlatjcl
    syl3anc
    @24
    cA
    @33
    cP
    cS
    c.or
    cK
    c.le
    @8
    @37
    3dim0.l
    3dim0.j
    3dim0.a
    hlexchb1
    syl131anc
    mpbid
    eqtr3d
    breq2d
    mtbird
    3jca
end
