include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "coc.mm"
include "cfv.mm"
include "cv.mm"
include "cjn.mm"
include "co.mm"
include "wrex.mm"
include "catm.mm"
include "simpr.mm"
include "wb.mm"
include "simpll1.mm"
include "eqid.mm"
include "atbase.mm"
include "adantl.mm"
include "lhpoc2N.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "adantr.mm"
include "cops.mm"
include "hlop.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "simpll3.mm"
include "opoccl.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "cvrcon3b.mm"
include "col.mm"
include "wceq.mm"
include "hlol.mm"
include "oldmm3N.mm"
include "breq2d.mm"
include "bitr2d.mm"
include "simpll2.mm"
include "oplecon3b.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "biimpa.mm"
include "ancomd.mm"
include "oveq2.mm"
include "rspcev.mm"
include "simpl1.mm"
include "simpl3.mm"
include "simpl2.mm"
include "opltcon3b.mm"
include "hlrelat3.mm"
include "syl31anc.mm"
include "r19.29a.mm"

theorem lhprelat3N
  let vw: setvar w
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume lhprelat3.b: |- B = ( Base ` K )
  assume lhprelat3.l: |- .<_ = ( le ` K )
  assume lhprelat3.s: |- .< = ( lt ` K )
  assume lhprelat3.m: |- ./\ = ( meet ` K )
  assume lhprelat3.c: |- C = ( <o ` K )
  assume lhprelat3.h: |- H = ( LHyp ` K )

  disjoint C w
  disjoint H w
  disjoint K w
  disjoint .<_ w
  disjoint ./\ w
  disjoint X w
  disjoint Y w
  disjoint B p
  disjoint p w
  disjoint C p
  disjoint H p
  disjoint K p
  disjoint .<_ p
  disjoint ./\ p
  disjoint .< p
  disjoint X p
  disjoint Y p
  assert |- ( ( ( K e. HL /\ X e. B /\ Y e. B ) /\ X .< Y ) -> E. w e. H ( X .<_ ( Y ./\ w ) /\ ( Y ./\ w ) C Y ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.lt
    wbr
    #
    wa
    #
    cY
    cK
    coc
    cfv
    #
    cfv
    #
    @7
    vp
    cv
    #
    cK
    cjn
    cfv
    #
    co
    #
    cC
    wbr
    #
    @10
    cX
    @6
    cfv
    #
    c.le
    wbr
    #
    wa
    #
    cX
    cY
    vw
    cv
    #
    c.an
    co
    #
    c.le
    wbr
    #
    @16
    cY
    cC
    wbr
    #
    wa
    #
    vw
    cH
    wrex
    #
    vp
    cK
    catm
    cfv
    #
    @5
    @8
    @21
    wcel
    #
    wa
    #
    @14
    wa
    #
    @8
    @6
    cfv
    #
    cH
    wcel
    #
    cX
    cY
    @25
    c.an
    co
    #
    c.le
    wbr
    #
    @27
    cY
    cC
    wbr
    #
    wa
    #
    @20
    @23
    @26
    @14
    @23
    @22
    @26
    @5
    @22
    simpr
    @23
    @0
    @8
    cB
    wcel
    #
    @22
    @26
    wb
    @0
    @1
    @2
    @4
    @22
    simpll1
    #
    @22
    @31
    @5
    @21
    cB
    @8
    cK
    lhprelat3.b
    @21
    eqid
    #
    atbase
    adantl
    #
    @21
    cB
    cH
    cK
    @6
    @8
    lhprelat3.b
    @6
    eqid
    #
    @33
    lhprelat3.h
    lhpoc2N
    syl2anc
    mpbid
    adantr
    @24
    @29
    @28
    @23
    @14
    @29
    @28
    wa
    @23
    @11
    @29
    @13
    @28
    @23
    @29
    @7
    @27
    @6
    cfv
    #
    cC
    wbr
    #
    @11
    @23
    cK
    cops
    wcel
    #
    @27
    cB
    wcel
    #
    @2
    @29
    @37
    wb
    @23
    @0
    @38
    @32
    cK
    hlop
    #
    syl
    #
    @23
    cK
    clat
    wcel
    #
    @2
    @25
    cB
    wcel
    #
    @39
    @23
    @0
    @42
    @32
    cK
    hllat
    syl
    @0
    @1
    @2
    @4
    @22
    simpll3
    #
    @23
    @38
    @31
    @43
    @41
    @34
    cB
    cK
    @6
    @8
    lhprelat3.b
    @35
    opoccl
    syl2anc
    cB
    cK
    c.an
    cY
    @25
    lhprelat3.b
    lhprelat3.m
    latmcl
    syl3anc
    #
    @44
    cB
    cC
    cK
    @6
    @27
    cY
    lhprelat3.b
    @35
    lhprelat3.c
    cvrcon3b
    syl3anc
    @23
    @36
    @10
    @7
    cC
    @23
    cK
    col
    wcel
    #
    @2
    @31
    @36
    @10
    wceq
    @23
    @0
    @46
    @32
    cK
    hlol
    syl
    @44
    @34
    cB
    @9
    cK
    c.an
    @6
    cY
    @8
    lhprelat3.b
    @9
    eqid
    #
    lhprelat3.m
    @35
    oldmm3N
    syl3anc
    #
    breq2d
    bitr2d
    @23
    @28
    @36
    @12
    c.le
    wbr
    #
    @13
    @23
    @38
    @1
    @39
    @28
    @49
    wb
    @41
    @0
    @1
    @2
    @4
    @22
    simpll2
    @45
    cB
    cK
    c.le
    @6
    cX
    @27
    lhprelat3.b
    lhprelat3.l
    @35
    oplecon3b
    syl3anc
    @23
    @36
    @10
    @12
    c.le
    @48
    breq1d
    bitr2d
    anbi12d
    biimpa
    ancomd
    @19
    @30
    vw
    @25
    cH
    @15
    @25
    wceq
    #
    @17
    @28
    @18
    @29
    @50
    @16
    @27
    cX
    c.le
    @15
    @25
    cY
    c.an
    oveq2
    #
    breq2d
    @50
    @16
    @27
    cY
    cC
    @51
    breq1d
    anbi12d
    rspcev
    syl2anc
    @5
    @0
    @7
    cB
    wcel
    #
    @12
    cB
    wcel
    #
    @7
    @12
    c.lt
    wbr
    #
    @14
    vp
    @21
    wrex
    @0
    @1
    @2
    @4
    simpl1
    #
    @5
    @38
    @2
    @52
    @5
    @0
    @38
    @55
    @40
    syl
    #
    @0
    @1
    @2
    @4
    simpl3
    #
    cB
    cK
    @6
    cY
    lhprelat3.b
    @35
    opoccl
    syl2anc
    @5
    @38
    @1
    @53
    @56
    @0
    @1
    @2
    @4
    simpl2
    #
    cB
    cK
    @6
    cX
    lhprelat3.b
    @35
    opoccl
    syl2anc
    @5
    @4
    @54
    @3
    @4
    simpr
    @5
    @38
    @1
    @2
    @4
    @54
    wb
    @56
    @58
    @57
    cB
    c.lt
    cK
    @6
    cX
    cY
    lhprelat3.b
    lhprelat3.s
    @35
    opltcon3b
    syl3anc
    mpbid
    @21
    cB
    cC
    c.lt
    @9
    cK
    c.le
    @7
    @12
    vp
    lhprelat3.b
    lhprelat3.l
    lhprelat3.s
    @47
    lhprelat3.c
    @33
    hlrelat3
    syl31anc
    r19.29a
end
