include "chlt.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "cp0.mm"
include "cfv.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "clln.mm"
include "simp1l.mm"
include "simp1r1.mm"
include "simp1r2.mm"
include "simp1r3.mm"
include "eqid.mm"
include "llni2.mm"
include "syl31anc.mm"
include "llnneat.mm"
include "syl2anc.mm"
include "llnn0.mm"
include "jca.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "pm4.56.mm"
include "bitri.mm"
include "sylib.mm"
include "simp3r2.mm"
include "simp3l.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "adantr.mm"
include "simp3r3.mm"
include "simpr.mm"
include "simp21.mm"
include "simp22.mm"
include "latlem12.mm"
include "ex.mm"
include "wi.mm"
include "cops.mm"
include "hlop.mm"
include "simprl.mm"
include "simprr.mm"
include "leat3.mm"
include "exp32.mm"
include "breq2.mm"
include "biimpa.mm"
include "ople0.mm"
include "syl5ib.mm"
include "imp.mm"
include "olcd.mm"
include "simp3r1.mm"
include "2atmat0.mm"
include "syl33anc.mm"
include "mpjaod.mm"
include "syld.mm"
include "mtod.mm"

theorem cdleme22b
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  assume cdleme22.l: |- .<_ = ( le ` K )
  assume cdleme22.j: |- .\/ = ( join ` K )
  assume cdleme22.m: |- ./\ = ( meet ` K )
  assume cdleme22.a: |- A = ( Atoms ` K )
  assume cdleme22.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ ( S e. A /\ T e. A /\ S =/= T ) ) /\ ( P e. A /\ Q e. A /\ P =/= Q ) /\ ( V e. A /\ ( ( T .\/ V ) =/= ( P .\/ Q ) /\ S .<_ ( T .\/ V ) /\ S .<_ ( P .\/ Q ) ) ) ) -> -. T .<_ ( P .\/ Q ) )

  proof
    cK
    chlt
    wcel
    #
    cS
    cA
    wcel
    #
    cT
    cA
    wcel
    #
    cS
    cT
    wne
    #
    w3a
    #
    wa
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
    cV
    cA
    wcel
    #
    cT
    cV
    c.or
    co
    #
    cP
    cQ
    c.or
    co
    #
    wne
    #
    cS
    @11
    c.le
    wbr
    #
    cS
    @12
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    w3a
    #
    cT
    @12
    c.le
    wbr
    #
    cS
    cT
    c.or
    co
    #
    cA
    wcel
    #
    @20
    cK
    cp0
    cfv
    #
    wceq
    #
    wo
    #
    @18
    @21
    wn
    #
    @20
    @22
    wne
    #
    wa
    #
    @24
    wn
    #
    @18
    @25
    @26
    @18
    @0
    @20
    cK
    clln
    cfv
    #
    wcel
    #
    @25
    @0
    @4
    @9
    @17
    simp1l
    #
    @18
    @0
    @1
    @2
    @3
    @30
    @31
    @1
    @2
    @3
    @0
    @9
    @17
    simp1r1
    #
    @1
    @2
    @3
    @0
    @9
    @17
    simp1r2
    #
    @1
    @2
    @3
    @0
    @9
    @17
    simp1r3
    cA
    cS
    cT
    c.or
    cK
    @29
    cdleme22.j
    cdleme22.a
    @29
    eqid
    #
    llni2
    syl31anc
    #
    cA
    cK
    @29
    @20
    cdleme22.a
    @34
    llnneat
    syl2anc
    @18
    @0
    @30
    @26
    @31
    @35
    cK
    @29
    @20
    @22
    @22
    eqid
    #
    @34
    llnn0
    syl2anc
    jca
    @27
    @25
    @23
    wn
    #
    wa
    @28
    @26
    @37
    @25
    @20
    @22
    df-ne
    anbi2i
    @21
    @23
    pm4.56
    bitri
    sylib
    @18
    @19
    @20
    @11
    @12
    c.an
    co
    #
    c.le
    wbr
    #
    @24
    @18
    @19
    @39
    @18
    @19
    wa
    #
    @20
    @11
    c.le
    wbr
    #
    @20
    @12
    c.le
    wbr
    #
    @39
    @18
    @41
    @19
    @18
    @14
    cT
    @11
    c.le
    wbr
    #
    @41
    @13
    @14
    @15
    @10
    @5
    @9
    simp3r2
    @18
    @0
    @2
    @10
    @43
    @31
    @33
    @5
    @9
    @10
    @16
    simp3l
    #
    cA
    cT
    cV
    c.or
    cK
    c.le
    cdleme22.l
    cdleme22.j
    cdleme22.a
    hlatlej1
    syl3anc
    @18
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
    cT
    @46
    wcel
    #
    @11
    @46
    wcel
    #
    @14
    @43
    wa
    @41
    wb
    @18
    @0
    @45
    @31
    cK
    hllat
    syl
    #
    @18
    @1
    @47
    @32
    cA
    @46
    cS
    cK
    @46
    eqid
    #
    cdleme22.a
    atbase
    syl
    #
    @18
    @2
    @48
    @33
    cA
    @46
    cT
    cK
    @51
    cdleme22.a
    atbase
    syl
    #
    @18
    @0
    @2
    @10
    @49
    @31
    @33
    @44
    cA
    @46
    c.or
    cK
    cT
    cV
    @51
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    #
    @46
    c.or
    cK
    c.le
    cS
    cT
    @11
    @51
    cdleme22.l
    cdleme22.j
    latjle12
    syl13anc
    mpbi2and
    adantr
    @40
    @15
    @19
    @42
    @18
    @15
    @19
    @13
    @14
    @15
    @10
    @5
    @9
    simp3r3
    adantr
    @18
    @19
    simpr
    @18
    @15
    @19
    wa
    @42
    wb
    #
    @19
    @18
    @45
    @47
    @48
    @12
    @46
    wcel
    #
    @55
    @50
    @52
    @53
    @18
    @0
    @6
    @7
    @56
    @31
    @5
    @6
    @7
    @8
    @17
    simp21
    #
    @5
    @6
    @7
    @8
    @17
    simp22
    #
    cA
    @46
    c.or
    cK
    cP
    cQ
    @51
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    #
    @46
    c.or
    cK
    c.le
    cS
    cT
    @12
    @51
    cdleme22.l
    cdleme22.j
    latjle12
    syl13anc
    adantr
    mpbi2and
    @18
    @41
    @42
    wa
    @39
    wb
    #
    @19
    @18
    @45
    @20
    @46
    wcel
    #
    @49
    @56
    @60
    @50
    @18
    @0
    @1
    @2
    @61
    @31
    @32
    @33
    cA
    @46
    c.or
    cK
    cS
    cT
    @51
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    #
    @54
    @59
    @46
    cK
    c.le
    c.an
    @20
    @11
    @12
    @51
    cdleme22.l
    cdleme22.m
    latlem12
    syl13anc
    adantr
    mpbi2and
    ex
    @18
    @38
    cA
    wcel
    #
    @39
    @24
    wi
    @38
    @22
    wceq
    #
    @18
    @63
    @39
    @24
    @18
    @63
    @39
    wa
    #
    wa
    cK
    cops
    wcel
    #
    @61
    @63
    @39
    @24
    @18
    @66
    @65
    @18
    @0
    @66
    @31
    cK
    hlop
    syl
    #
    adantr
    @18
    @61
    @65
    @62
    adantr
    @18
    @63
    @39
    simprl
    @18
    @63
    @39
    simprr
    cA
    @46
    @38
    cK
    c.le
    @20
    @22
    @51
    cdleme22.l
    @36
    cdleme22.a
    leat3
    syl31anc
    exp32
    @18
    @64
    @39
    @24
    @18
    @64
    @39
    wa
    #
    wa
    @23
    @21
    @18
    @68
    @23
    @68
    @20
    @22
    c.le
    wbr
    #
    @18
    @23
    @64
    @39
    @69
    @38
    @22
    @20
    c.le
    breq2
    biimpa
    @18
    @66
    @61
    @69
    @23
    wb
    @67
    @62
    @46
    cK
    c.le
    @20
    @22
    @51
    cdleme22.l
    @36
    ople0
    syl2anc
    syl5ib
    imp
    olcd
    exp32
    @18
    @0
    @2
    @10
    @6
    @7
    @13
    @63
    @64
    wo
    @31
    @33
    @44
    @57
    @58
    @13
    @14
    @15
    @10
    @5
    @9
    simp3r1
    cA
    cT
    cV
    cP
    cQ
    c.or
    cK
    c.an
    @22
    cdleme22.j
    cdleme22.m
    @36
    cdleme22.a
    2atmat0
    syl33anc
    mpjaod
    syld
    mtod
end
