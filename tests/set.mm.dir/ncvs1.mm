include "cnvc.mm"
include "ccvs.mm"
include "cin.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "w3a.mm"
include "cmul.mm"
include "cr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3.mm"
include "cngp.mm"
include "elin.mm"
include "cnlm.mm"
include "nvcnlm.mm"
include "nlmngp.mm"
include "syl.mm"
include "adantr.mm"
include "sylbi.mm"
include "simpl.mm"
include "anim12i.mm"
include "nmcl.mm"
include "wb.mm"
include "nmeq0.mm"
include "bicomd.mm"
include "sylan.mm"
include "necon3bid.mm"
include "biimpd.mm"
include "impr.mm"
include "rereccld.mm"
include "3adant3.mm"
include "elind.mm"
include "clt.mm"
include "1re.mm"
include "0le1.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "simprr.mm"
include "nmgt0.mm"
include "mpbid.mm"
include "jca32.mm"
include "divge0.mm"
include "simp2l.mm"
include "ncvsge0.mm"
include "syl121anc.mm"
include "recnd.mm"
include "recid2d.mm"
include "eqtrd.mm"

theorem ncvs1
  let cA: class A
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cN: class N
  let cX: class X
  let c.0: class .0.
  assume ncvs1.x: |- X = ( Base ` G )
  assume ncvs1.n: |- N = ( norm ` G )
  assume ncvs1.z: |- .0. = ( 0g ` G )
  assume ncvs1.s: |- .x. = ( .s ` G )
  assume ncvs1.f: |- F = ( Scalar ` G )
  assume ncvs1.k: |- K = ( Base ` F )


  assert |- ( ( G e. ( NrmVec i^i CVec ) /\ ( A e. X /\ A =/= .0. ) /\ ( 1 / ( N ` A ) ) e. K ) -> ( N ` ( ( 1 / ( N ` A ) ) .x. A ) ) = 1 )

  proof
    cG
    cnvc
    ccvs
    cin
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    c.0
    wne
    #
    wa
    #
    c1
    cA
    cN
    cfv
    #
    cdiv
    co
    #
    cK
    wcel
    #
    w3a
    #
    @5
    cA
    c.x
    co
    cN
    cfv
    #
    @5
    @4
    cmul
    co
    #
    c1
    @7
    @0
    @5
    cK
    cr
    cin
    wcel
    cc0
    @5
    cle
    wbr
    #
    @1
    @8
    @9
    wceq
    @0
    @3
    @6
    simp1
    @7
    cK
    cr
    @5
    @0
    @3
    @6
    simp3
    @0
    @3
    @5
    cr
    wcel
    @6
    @0
    @3
    wa
    #
    @4
    @11
    cG
    cngp
    wcel
    #
    @1
    wa
    #
    @4
    cr
    wcel
    #
    @0
    @12
    @3
    @1
    @0
    cG
    cnvc
    wcel
    #
    cG
    ccvs
    wcel
    #
    wa
    @12
    cG
    cnvc
    ccvs
    elin
    @15
    @12
    @16
    @15
    cG
    cnlm
    wcel
    @12
    cG
    nvcnlm
    cG
    nlmngp
    syl
    adantr
    sylbi
    #
    @1
    @2
    simpl
    anim12i
    #
    cA
    cG
    cN
    cX
    ncvs1.x
    ncvs1.n
    nmcl
    #
    syl
    #
    @0
    @1
    @2
    @4
    cc0
    wne
    #
    @0
    @1
    wa
    #
    @2
    @21
    @22
    cA
    c.0
    @4
    cc0
    @0
    @12
    @1
    cA
    c.0
    wceq
    #
    @4
    cc0
    wceq
    #
    wb
    @17
    @13
    @24
    @23
    cA
    cG
    cN
    cX
    c.0
    ncvs1.x
    ncvs1.n
    ncvs1.z
    nmeq0
    bicomd
    sylan
    necon3bid
    biimpd
    impr
    #
    rereccld
    3adant3
    elind
    @7
    c1
    cr
    wcel
    #
    cc0
    c1
    cle
    wbr
    #
    wa
    #
    @14
    cc0
    @4
    clt
    wbr
    #
    wa
    wa
    #
    @10
    @0
    @3
    @30
    @6
    @11
    @28
    @14
    @29
    @28
    @11
    @26
    @27
    1re
    0le1
    pm3.2i
    a1i
    @20
    @11
    @2
    @29
    @0
    @1
    @2
    simprr
    @11
    @13
    @2
    @29
    wb
    @18
    cA
    cG
    cN
    cX
    c.0
    ncvs1.x
    ncvs1.n
    ncvs1.z
    nmgt0
    syl
    mpbid
    jca32
    3adant3
    c1
    @4
    divge0
    syl
    @0
    @1
    @2
    @6
    simp2l
    @5
    cA
    c.x
    cF
    cK
    cN
    cX
    cG
    ncvs1.x
    ncvs1.n
    ncvs1.s
    ncvs1.f
    ncvs1.k
    ncvsge0
    syl121anc
    @7
    @4
    @7
    @4
    @7
    @13
    @14
    @0
    @3
    @13
    @6
    @18
    3adant3
    @19
    syl
    recnd
    @0
    @3
    @21
    @6
    @25
    3adant3
    recid2d
    eqtrd
end
