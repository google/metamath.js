include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "wo.mm"
include "w3o.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl12.mm"
include "3jca.mm"
include "simpl3.mm"
include "simpr.mm"
include "4atlem3.mm"
include "syl31anc.mm"
include "wb.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simpl11.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "latlej1.mm"
include "wceq.mm"
include "latjass.mm"
include "syl13anc.mm"
include "breqtrrd.mm"
include "biortn.mm"
include "orbi1d.mm"
include "mpbird.mm"
include "3orass.mm"
include "sylibr.mm"

theorem 4atlem3a
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  assume 4at.l: |- .<_ = ( le ` K )
  assume 4at.j: |- .\/ = ( join ` K )
  assume 4at.a: |- A = ( Atoms ` K )


  assert |- ( ( ( ( K e. HL /\ P e. A /\ Q e. A ) /\ ( R e. A /\ S e. A ) /\ ( U e. A /\ V e. A ) ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) /\ -. S .<_ ( ( P .\/ Q ) .\/ R ) ) ) -> ( -. Q .<_ ( ( P .\/ U ) .\/ V ) \/ -. R .<_ ( ( P .\/ U ) .\/ V ) \/ -. S .<_ ( ( P .\/ U ) .\/ V ) ) )

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
    cU
    cA
    wcel
    #
    cV
    cA
    wcel
    #
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    cS
    @11
    cR
    c.or
    co
    c.le
    wbr
    wn
    w3a
    #
    wa
    #
    cQ
    cP
    cU
    c.or
    co
    cV
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cR
    @14
    c.le
    wbr
    wn
    #
    cS
    @14
    c.le
    wbr
    wn
    #
    wo
    #
    wo
    #
    @15
    @16
    @17
    w3o
    @13
    @19
    cP
    @14
    c.le
    wbr
    #
    wn
    @15
    wo
    #
    @18
    wo
    #
    @13
    @3
    @4
    @5
    @1
    w3a
    @9
    @12
    @22
    @3
    @6
    @9
    @12
    simpl1
    @13
    @4
    @5
    @1
    @4
    @5
    @3
    @9
    @12
    simpl2l
    @4
    @5
    @3
    @9
    @12
    simpl2r
    @0
    @1
    @2
    @6
    @9
    @12
    simpl12
    #
    3jca
    @3
    @6
    @9
    @12
    simpl3
    @10
    @12
    simpr
    cA
    cP
    cQ
    cR
    cS
    cP
    cU
    c.or
    cK
    c.le
    cV
    4at.l
    4at.j
    4at.a
    4atlem3
    syl31anc
    @13
    @15
    @21
    @18
    @13
    @20
    @15
    @21
    wb
    @13
    cP
    cP
    cU
    cV
    c.or
    co
    #
    c.or
    co
    #
    @14
    c.le
    @13
    cK
    clat
    wcel
    #
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @24
    @27
    wcel
    #
    cP
    @25
    c.le
    wbr
    @13
    @0
    @26
    @0
    @1
    @2
    @6
    @9
    @12
    simpl11
    #
    cK
    hllat
    syl
    #
    @13
    @1
    @28
    @23
    cA
    @27
    cP
    cK
    @27
    eqid
    #
    4at.a
    atbase
    syl
    #
    @13
    @0
    @7
    @8
    @29
    @30
    @7
    @8
    @3
    @6
    @12
    simpl3l
    #
    @7
    @8
    @3
    @6
    @12
    simpl3r
    #
    cA
    @27
    c.or
    cK
    cU
    cV
    @32
    4at.j
    4at.a
    hlatjcl
    syl3anc
    @27
    c.or
    cK
    c.le
    cP
    @24
    @32
    4at.l
    4at.j
    latlej1
    syl3anc
    @13
    @26
    @28
    cU
    @27
    wcel
    #
    cV
    @27
    wcel
    #
    @14
    @25
    wceq
    @31
    @33
    @13
    @7
    @36
    @34
    cA
    @27
    cU
    cK
    @32
    4at.a
    atbase
    syl
    @13
    @8
    @37
    @35
    cA
    @27
    cV
    cK
    @32
    4at.a
    atbase
    syl
    @27
    c.or
    cK
    cP
    cU
    cV
    @32
    4at.j
    latjass
    syl13anc
    breqtrrd
    @20
    @15
    biortn
    syl
    orbi1d
    mpbird
    @15
    @16
    @17
    3orass
    sylibr
end
