include "chlt.mm"
include "wcel.mm"
include "cv.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wrex.mm"
include "ccvr.mm"
include "cfv.mm"
include "wa.mm"
include "eqid.mm"
include "athgt.mm"
include "wb.mm"
include "df-3an.mm"
include "cbs.mm"
include "simpll1.mm"
include "hlatjcl.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "cvr1.mm"
include "syl3anc.mm"
include "anbi2d.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "ad2antlr.mm"
include "latjcl.mm"
include "simpr.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "r19.42v.mm"
include "anass.mm"
include "bitri.mm"
include "syl6bb.mm"
include "atcvr1.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "3expb.mm"
include "2rexbidva.mm"
include "mpbird.mm"

theorem 3dim0
  let cA: class A
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let vp: setvar p
  assume 3dim0.j: |- .\/ = ( join ` K )
  assume 3dim0.l: |- .<_ = ( le ` K )
  assume 3dim0.a: |- A = ( Atoms ` K )

  disjoint p q
  disjoint p r
  disjoint p s
  disjoint K p
  disjoint q r
  disjoint q s
  disjoint K q
  disjoint r s
  disjoint K r
  disjoint K s
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint A p
  disjoint q r
  disjoint q s
  disjoint A q
  disjoint r s
  disjoint A r
  disjoint A s
  disjoint .\/ r
  disjoint .\/ s
  assert |- ( K e. HL -> E. p e. A E. q e. A E. r e. A E. s e. A ( p =/= q /\ -. r .<_ ( p .\/ q ) /\ -. s .<_ ( ( p .\/ q ) .\/ r ) ) )

  proof
    cK
    chlt
    wcel
    #
    vp
    cv
    #
    vq
    cv
    #
    wne
    #
    vr
    cv
    #
    @1
    @2
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    vs
    cv
    #
    @5
    @4
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    vs
    cA
    wrex
    #
    vr
    cA
    wrex
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    @1
    @5
    cK
    ccvr
    cfv
    #
    wbr
    #
    @5
    @8
    @13
    wbr
    #
    @8
    @8
    @7
    c.or
    co
    @13
    wbr
    #
    vs
    cA
    wrex
    #
    wa
    #
    vr
    cA
    wrex
    #
    wa
    #
    vq
    cA
    wrex
    vp
    cA
    wrex
    cA
    @13
    c.or
    cK
    vs
    vr
    vq
    vp
    3dim0.j
    @13
    eqid
    #
    3dim0.a
    athgt
    @0
    @12
    @20
    vp
    vq
    cA
    cA
    @0
    @1
    cA
    wcel
    #
    @2
    cA
    wcel
    #
    @12
    @20
    wb
    @0
    @22
    @23
    w3a
    #
    @12
    @3
    @19
    wa
    #
    @20
    @24
    @12
    @3
    @18
    wa
    #
    vr
    cA
    wrex
    @25
    @24
    @11
    @26
    vr
    cA
    @24
    @4
    cA
    wcel
    #
    wa
    #
    @11
    @3
    @15
    wa
    #
    @16
    wa
    #
    vs
    cA
    wrex
    #
    @26
    @28
    @10
    @30
    vs
    cA
    @10
    @3
    @6
    wa
    #
    @9
    wa
    @28
    @7
    cA
    wcel
    #
    wa
    #
    @30
    @3
    @6
    @9
    df-3an
    @34
    @32
    @29
    @9
    @16
    @34
    @6
    @15
    @3
    @34
    @0
    @5
    cK
    cbs
    cfv
    #
    wcel
    #
    @27
    @6
    @15
    wb
    @0
    @22
    @23
    @27
    @33
    simpll1
    #
    @24
    @36
    @27
    @33
    cA
    @35
    c.or
    cK
    @1
    @2
    @35
    eqid
    #
    3dim0.j
    3dim0.a
    hlatjcl
    ad2antrr
    #
    @24
    @27
    @33
    simplr
    cA
    @35
    @13
    @4
    c.or
    cK
    c.le
    @5
    @38
    3dim0.l
    3dim0.j
    @21
    3dim0.a
    cvr1
    syl3anc
    anbi2d
    @34
    @0
    @8
    @35
    wcel
    #
    @33
    @9
    @16
    wb
    @37
    @34
    cK
    clat
    wcel
    #
    @36
    @4
    @35
    wcel
    #
    @40
    @34
    @0
    @41
    @37
    cK
    hllat
    syl
    @39
    @27
    @42
    @24
    @33
    cA
    @35
    @4
    cK
    @38
    3dim0.a
    atbase
    ad2antlr
    @35
    c.or
    cK
    @5
    @4
    @38
    3dim0.j
    latjcl
    syl3anc
    @28
    @33
    simpr
    cA
    @35
    @13
    @7
    c.or
    cK
    c.le
    @8
    @38
    3dim0.l
    3dim0.j
    @21
    3dim0.a
    cvr1
    syl3anc
    anbi12d
    syl5bb
    rexbidva
    @31
    @29
    @17
    wa
    @26
    @29
    @16
    vs
    cA
    r19.42v
    @3
    @15
    @17
    anass
    bitri
    syl6bb
    rexbidva
    @3
    @18
    vr
    cA
    r19.42v
    syl6bb
    @24
    @3
    @14
    @19
    cA
    @13
    @1
    @2
    c.or
    cK
    3dim0.j
    @21
    3dim0.a
    atcvr1
    anbi1d
    bitrd
    3expb
    2rexbidva
    mpbird
end
