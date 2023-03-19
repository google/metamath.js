include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "coc.mm"
include "cfv.mm"
include "catm.mm"
include "simp1l.mm"
include "simp1r.mm"
include "eqid.mm"
include "lhpocat.mm"
include "syl2anc.mm"
include "cops.mm"
include "hlop.mm"
include "syl.mm"
include "simp2l.mm"
include "opoccl.mm"
include "simp2r.mm"
include "simp3.mm"
include "wb.mm"
include "oplecon3b.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "atmod1i2.mm"
include "syl131anc.mm"
include "clat.mm"
include "hllat.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latjcl.mm"
include "opcon3b.mm"
include "col.mm"
include "hlol.mm"
include "oldmm1.mm"
include "oldmj1.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem lhpmod2i2
  let cB: class B
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lhpmod.b: |- B = ( Base ` K )
  assume lhpmod.l: |- .<_ = ( le ` K )
  assume lhpmod.j: |- .\/ = ( join ` K )
  assume lhpmod.m: |- ./\ = ( meet ` K )
  assume lhpmod.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ Y e. B ) /\ Y .<_ X ) -> ( ( X ./\ W ) .\/ Y ) = ( X ./\ ( W .\/ Y ) ) )

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
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cY
    cX
    c.le
    wbr
    #
    w3a
    #
    cX
    cW
    c.an
    co
    #
    cY
    c.or
    co
    #
    cX
    cW
    cY
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    cX
    cK
    coc
    cfv
    #
    cfv
    #
    cW
    @13
    cfv
    #
    cY
    @13
    cfv
    #
    c.an
    co
    #
    c.or
    co
    #
    @14
    @15
    c.or
    co
    #
    @16
    c.an
    co
    #
    wceq
    #
    @7
    @0
    @15
    cK
    catm
    cfv
    #
    wcel
    #
    @14
    cB
    wcel
    #
    @16
    cB
    wcel
    #
    @14
    @16
    c.le
    wbr
    #
    @21
    @0
    @1
    @5
    @6
    simp1l
    #
    @7
    @0
    @1
    @23
    @27
    @0
    @1
    @5
    @6
    simp1r
    #
    @22
    cH
    cK
    @13
    cW
    @13
    eqid
    #
    @22
    eqid
    #
    lhpmod.h
    lhpocat
    syl2anc
    @7
    cK
    cops
    wcel
    #
    @3
    @24
    @7
    @0
    @31
    @27
    cK
    hlop
    syl
    #
    @2
    @3
    @4
    @6
    simp2l
    #
    cB
    cK
    @13
    cX
    lhpmod.b
    @29
    opoccl
    syl2anc
    @7
    @31
    @4
    @25
    @32
    @2
    @3
    @4
    @6
    simp2r
    #
    cB
    cK
    @13
    cY
    lhpmod.b
    @29
    opoccl
    syl2anc
    @7
    @6
    @26
    @2
    @5
    @6
    simp3
    @7
    @31
    @4
    @3
    @6
    @26
    wb
    @32
    @34
    @33
    cB
    cK
    c.le
    @13
    cY
    cX
    lhpmod.b
    lhpmod.l
    @29
    oplecon3b
    syl3anc
    mpbid
    @22
    cB
    @15
    c.or
    cK
    c.le
    c.an
    @14
    @16
    lhpmod.b
    lhpmod.l
    lhpmod.j
    lhpmod.m
    @30
    atmod1i2
    syl131anc
    @7
    @12
    @11
    @13
    cfv
    #
    @9
    @13
    cfv
    #
    wceq
    #
    @21
    @7
    @31
    @9
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @12
    @37
    wb
    @32
    @7
    cK
    clat
    wcel
    #
    @8
    cB
    wcel
    #
    @4
    @38
    @7
    @0
    @40
    @27
    cK
    hllat
    syl
    #
    @7
    @40
    @3
    cW
    cB
    wcel
    #
    @41
    @42
    @33
    @7
    @1
    @43
    @28
    cB
    cH
    cK
    cW
    lhpmod.b
    lhpmod.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    cX
    cW
    lhpmod.b
    lhpmod.m
    latmcl
    syl3anc
    #
    @34
    cB
    c.or
    cK
    @8
    cY
    lhpmod.b
    lhpmod.j
    latjcl
    syl3anc
    @7
    @40
    @3
    @10
    cB
    wcel
    #
    @39
    @42
    @33
    @7
    @40
    @43
    @4
    @46
    @42
    @44
    @34
    cB
    c.or
    cK
    cW
    cY
    lhpmod.b
    lhpmod.j
    latjcl
    syl3anc
    #
    cB
    cK
    c.an
    cX
    @10
    lhpmod.b
    lhpmod.m
    latmcl
    syl3anc
    cB
    cK
    @13
    @9
    @11
    lhpmod.b
    @29
    opcon3b
    syl3anc
    @7
    @35
    @18
    @36
    @20
    @7
    @35
    @14
    @10
    @13
    cfv
    #
    c.or
    co
    #
    @18
    @7
    cK
    col
    wcel
    #
    @3
    @46
    @35
    @49
    wceq
    @7
    @0
    @50
    @27
    cK
    hlol
    syl
    #
    @33
    @47
    cB
    c.or
    cK
    c.an
    @13
    cX
    @10
    lhpmod.b
    lhpmod.j
    lhpmod.m
    @29
    oldmm1
    syl3anc
    @7
    @48
    @17
    @14
    c.or
    @7
    @50
    @43
    @4
    @48
    @17
    wceq
    @51
    @44
    @34
    cB
    c.or
    cK
    c.an
    @13
    cW
    cY
    lhpmod.b
    lhpmod.j
    lhpmod.m
    @29
    oldmj1
    syl3anc
    oveq2d
    eqtrd
    @7
    @36
    @8
    @13
    cfv
    #
    @16
    c.an
    co
    #
    @20
    @7
    @50
    @41
    @4
    @36
    @53
    wceq
    @51
    @45
    @34
    cB
    c.or
    cK
    c.an
    @13
    @8
    cY
    lhpmod.b
    lhpmod.j
    lhpmod.m
    @29
    oldmj1
    syl3anc
    @7
    @52
    @19
    @16
    c.an
    @7
    @50
    @3
    @43
    @52
    @19
    wceq
    @51
    @33
    @44
    cB
    c.or
    cK
    c.an
    @13
    cX
    cW
    lhpmod.b
    lhpmod.j
    lhpmod.m
    @29
    oldmm1
    syl3anc
    oveq1d
    eqtrd
    eqeq12d
    bitrd
    mpbird
end
