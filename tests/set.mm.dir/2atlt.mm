include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cjn.mm"
include "cfv.mm"
include "co.mm"
include "cple.mm"
include "wrex.mm"
include "wne.mm"
include "atbase.mm"
include "eqid.mm"
include "hlrelat.mm"
include "syl3anl2.mm"
include "ccvr.mm"
include "simp3l.mm"
include "wb.mm"
include "simp1l1.mm"
include "simp1l2.mm"
include "simp2.mm"
include "atltcvr.mm"
include "syl13anc.mm"
include "mpbid.mm"
include "atcvr1.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "necomd.mm"
include "atlt.mm"
include "clat.mm"
include "wceq.mm"
include "hllat.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "latjcom.mm"
include "breqtrrd.mm"
include "simp3r.mm"
include "cpo.mm"
include "wi.mm"
include "hlpos.mm"
include "latjcl.mm"
include "simp1l3.mm"
include "pltletr.mm"
include "mp2and.mm"
include "jca.mm"
include "3exp.mm"
include "reximdvai.mm"
include "mpd.mm"

theorem 2atlt
  let cA: class A
  let cB: class B
  let cP: class P
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let vq: setvar q
  assume 2atomslt.b: |- B = ( Base ` K )
  assume 2atomslt.s: |- .< = ( lt ` K )
  assume 2atomslt.a: |- A = ( Atoms ` K )

  disjoint A q
  disjoint B q
  disjoint K q
  disjoint P q
  disjoint .< q
  disjoint X q
  assert |- ( ( ( K e. HL /\ P e. A /\ X e. B ) /\ P .< X ) -> E. q e. A ( q =/= P /\ q .< X ) )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    cP
    cX
    c.lt
    wbr
    #
    wa
    #
    cP
    cP
    vq
    cv
    #
    cK
    cjn
    cfv
    #
    co
    #
    c.lt
    wbr
    #
    @7
    cX
    cK
    cple
    cfv
    #
    wbr
    #
    wa
    #
    vq
    cA
    wrex
    #
    @5
    cP
    wne
    #
    @5
    cX
    c.lt
    wbr
    #
    wa
    #
    vq
    cA
    wrex
    @1
    @0
    cP
    cB
    wcel
    #
    @2
    @3
    @12
    cA
    cB
    cP
    cK
    2atomslt.b
    2atomslt.a
    atbase
    #
    cA
    cB
    c.lt
    @6
    cK
    @9
    cP
    cX
    vq
    2atomslt.b
    @9
    eqid
    #
    2atomslt.s
    @6
    eqid
    #
    2atomslt.a
    hlrelat
    syl3anl2
    @4
    @11
    @15
    vq
    cA
    @4
    @5
    cA
    wcel
    #
    @11
    @15
    @4
    @20
    @11
    w3a
    #
    @13
    @14
    @21
    cP
    @5
    @21
    cP
    @5
    wne
    #
    cP
    @7
    cK
    ccvr
    cfv
    #
    wbr
    #
    @21
    @8
    @24
    @4
    @20
    @8
    @10
    simp3l
    @21
    @0
    @1
    @1
    @20
    @8
    @24
    wb
    @0
    @1
    @2
    @3
    @20
    @11
    simp1l1
    #
    @0
    @1
    @2
    @3
    @20
    @11
    simp1l2
    #
    @26
    @4
    @20
    @11
    simp2
    #
    cA
    @23
    cP
    cP
    @5
    c.lt
    @6
    cK
    2atomslt.s
    @19
    2atomslt.a
    @23
    eqid
    #
    atltcvr
    syl13anc
    mpbid
    @21
    @0
    @1
    @20
    @22
    @24
    wb
    @25
    @26
    @27
    cA
    @23
    cP
    @5
    @6
    cK
    @19
    @28
    2atomslt.a
    atcvr1
    syl3anc
    mpbird
    necomd
    #
    @21
    @5
    @7
    c.lt
    wbr
    #
    @10
    @14
    @21
    @5
    @5
    cP
    @6
    co
    #
    @7
    c.lt
    @21
    @5
    @31
    c.lt
    wbr
    #
    @13
    @29
    @21
    @0
    @20
    @1
    @32
    @13
    wb
    @25
    @27
    @26
    cA
    @5
    cP
    c.lt
    @6
    cK
    2atomslt.s
    @19
    2atomslt.a
    atlt
    syl3anc
    mpbird
    @21
    cK
    clat
    wcel
    #
    @16
    @5
    cB
    wcel
    #
    @7
    @31
    wceq
    @21
    @0
    @33
    @25
    cK
    hllat
    syl
    #
    @21
    @1
    @16
    @26
    @17
    syl
    #
    @20
    @4
    @34
    @11
    cA
    cB
    @5
    cK
    2atomslt.b
    2atomslt.a
    atbase
    3ad2ant2
    #
    cB
    @6
    cK
    cP
    @5
    2atomslt.b
    @19
    latjcom
    syl3anc
    breqtrrd
    @4
    @20
    @8
    @10
    simp3r
    @21
    cK
    cpo
    wcel
    #
    @34
    @7
    cB
    wcel
    #
    @2
    @30
    @10
    wa
    @14
    wi
    @21
    @0
    @38
    @25
    cK
    hlpos
    syl
    @37
    @21
    @33
    @16
    @34
    @39
    @35
    @36
    @37
    cB
    @6
    cK
    cP
    @5
    2atomslt.b
    @19
    latjcl
    syl3anc
    @0
    @1
    @2
    @3
    @20
    @11
    simp1l3
    cB
    c.lt
    cK
    @9
    @5
    @7
    cX
    2atomslt.b
    @18
    2atomslt.s
    pltletr
    syl13anc
    mp2and
    jca
    3exp
    reximdvai
    mpd
end
