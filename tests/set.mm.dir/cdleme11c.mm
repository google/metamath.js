include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp3l.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp23.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "adantr.mm"
include "wceq.mm"
include "jca.mm"
include "simp21.mm"
include "simp22.mm"
include "simp3r.mm"
include "cdleme11a.mm"
include "syl122anc.mm"
include "breq2d.mm"
include "wi.mm"
include "simp21l.mm"
include "cdleme0b.mm"
include "necomd.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "sylbird.mm"
include "imp.mm"
include "hlatlej2.mm"
include "cdleme0cp.mm"
include "syl12anc.mm"
include "breqtrrd.mm"
include "wb.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "latnlej1r.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"
include "ex.mm"
include "syld.mm"
include "mtod.mm"

theorem cdleme11c
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme11.l: |- .<_ = ( le ` K )
  assume cdleme11.j: |- .\/ = ( join ` K )
  assume cdleme11.m: |- ./\ = ( meet ` K )
  assume cdleme11.a: |- A = ( Atoms ` K )
  assume cdleme11.h: |- H = ( LHyp ` K )
  assume cdleme11.u: |- U = ( ( P .\/ Q ) ./\ W )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( ( S e. A /\ -. S .<_ W ) /\ T e. A /\ P =/= Q ) /\ ( -. S .<_ ( P .\/ Q ) /\ U .<_ ( S .\/ T ) ) ) -> -. P .<_ ( S .\/ T ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
    #
    w3a
    #
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cT
    cA
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    cU
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cP
    @17
    c.le
    wbr
    #
    @15
    @7
    @13
    @16
    @18
    simp3l
    #
    @20
    @21
    cP
    cS
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @15
    @20
    @21
    @24
    @20
    @21
    wa
    #
    cP
    cP
    cU
    c.or
    co
    #
    @23
    c.le
    @20
    cP
    @26
    c.le
    wbr
    #
    @21
    @20
    @0
    @3
    cU
    cA
    wcel
    #
    @27
    @0
    @1
    @5
    @6
    @13
    @19
    simp11l
    #
    @3
    @4
    @2
    @6
    @13
    @19
    simp12l
    #
    @20
    @2
    @5
    @6
    @12
    @28
    @2
    @5
    @6
    @13
    @19
    simp11
    #
    @2
    @5
    @6
    @13
    @19
    simp12
    #
    @2
    @5
    @6
    @13
    @19
    simp13
    #
    @7
    @10
    @11
    @12
    @19
    simp23
    #
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme11.h
    cdleme11.u
    lhpat2
    syl112anc
    #
    cA
    cP
    cU
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    hlatlej1
    syl3anc
    adantr
    @25
    @23
    @26
    c.le
    wbr
    #
    @23
    @26
    wceq
    #
    @25
    cS
    @26
    c.le
    wbr
    #
    cQ
    @26
    c.le
    wbr
    #
    @36
    @20
    @21
    @38
    @20
    @21
    cP
    cS
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    @38
    @20
    @40
    @17
    cP
    c.le
    @20
    @2
    @5
    @6
    @12
    wa
    @10
    @11
    @18
    wa
    @40
    @17
    wceq
    @31
    @32
    @20
    @6
    @12
    @33
    @34
    jca
    @7
    @10
    @11
    @12
    @19
    simp21
    @20
    @11
    @18
    @7
    @10
    @11
    @12
    @19
    simp22
    @7
    @13
    @16
    @18
    simp3r
    jca
    cA
    cP
    cQ
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme11.h
    cdleme11.u
    cdleme11a
    syl122anc
    breq2d
    @20
    @0
    @3
    @8
    @28
    cP
    cU
    wne
    @41
    @38
    wi
    @29
    @30
    @8
    @9
    @11
    @12
    @7
    @19
    simp21l
    #
    @35
    @20
    cU
    cP
    @20
    @2
    @5
    @6
    cU
    cP
    wne
    @31
    @32
    @33
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme11.h
    cdleme11.u
    cdleme0b
    syl3anc
    necomd
    cA
    cP
    cS
    cU
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    hlatexch2
    syl131anc
    sylbird
    imp
    @20
    @39
    @21
    @20
    cQ
    @14
    @26
    c.le
    @20
    @0
    @3
    @6
    cQ
    @14
    c.le
    wbr
    @29
    @30
    @33
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    hlatlej2
    syl3anc
    @20
    @2
    @5
    @6
    @26
    @14
    wceq
    @31
    @32
    @33
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme11.h
    cdleme11.u
    cdleme0cp
    syl12anc
    breqtrrd
    adantr
    @20
    @38
    @39
    wa
    @36
    wb
    #
    @21
    @20
    cK
    clat
    wcel
    #
    cS
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    @45
    wcel
    #
    @26
    @45
    wcel
    #
    @43
    @20
    @0
    @44
    @29
    cK
    hllat
    syl
    #
    @20
    @8
    @46
    @42
    cA
    @45
    cS
    cK
    @45
    eqid
    #
    cdleme11.a
    atbase
    syl
    #
    @20
    @6
    @47
    @33
    cA
    @45
    cQ
    cK
    @50
    cdleme11.a
    atbase
    syl
    #
    @20
    @0
    @3
    @28
    @48
    @29
    @30
    @35
    cA
    @45
    c.or
    cK
    cP
    cU
    @50
    cdleme11.j
    cdleme11.a
    hlatjcl
    syl3anc
    @45
    c.or
    cK
    c.le
    cS
    cQ
    @26
    @50
    cdleme11.l
    cdleme11.j
    latjle12
    syl13anc
    adantr
    mpbi2and
    @20
    @36
    @37
    wb
    #
    @21
    @20
    @0
    @8
    @6
    cS
    cQ
    wne
    #
    @3
    @28
    @53
    @29
    @42
    @33
    @20
    @44
    @46
    cP
    @45
    wcel
    #
    @47
    @16
    @54
    @49
    @51
    @20
    @3
    @55
    @30
    cA
    @45
    cP
    cK
    @50
    cdleme11.a
    atbase
    syl
    @52
    @22
    @45
    c.or
    cK
    c.le
    cS
    cP
    cQ
    @50
    cdleme11.l
    cdleme11.j
    latnlej1r
    syl131anc
    @30
    @35
    cA
    cS
    cQ
    cP
    cU
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    ps-1
    syl132anc
    adantr
    mpbid
    breqtrrd
    ex
    @20
    @0
    @3
    @8
    @6
    @12
    @24
    @15
    wi
    @29
    @30
    @42
    @33
    @34
    cA
    cP
    cS
    cQ
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    hlatexch2
    syl131anc
    syld
    mtod
end
