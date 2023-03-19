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
include "lhpbase.mm"
include "oplecon3b.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "atmod2i1.mm"
include "syl131anc.mm"
include "clat.mm"
include "hllat.mm"
include "latmcl.mm"
include "latjcl.mm"
include "opcon3b.mm"
include "col.mm"
include "hlol.mm"
include "oldmm1.mm"
include "oldmj1.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "bitrd.mm"
include "mpbird.mm"

theorem lhpmod6i1
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ Y e. B ) /\ X .<_ W ) -> ( X .\/ ( Y ./\ W ) ) = ( ( X .\/ Y ) ./\ W ) )

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
    cX
    cW
    c.le
    wbr
    #
    w3a
    #
    cX
    cY
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    cY
    c.or
    co
    #
    cW
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
    cY
    @13
    cfv
    #
    c.an
    co
    #
    cW
    @13
    cfv
    #
    c.or
    co
    #
    @14
    @15
    @17
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    @7
    @0
    @17
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
    @15
    cB
    wcel
    #
    @17
    @14
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
    @3
    cW
    cB
    wcel
    #
    @6
    @26
    wb
    @32
    @33
    @7
    @1
    @35
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
    c.le
    @13
    cX
    cW
    lhpmod.b
    lhpmod.l
    @29
    oplecon3b
    syl3anc
    mpbid
    @22
    cB
    @17
    c.or
    cK
    c.le
    c.an
    @14
    @15
    lhpmod.b
    lhpmod.l
    lhpmod.j
    lhpmod.m
    @30
    atmod2i1
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
    @39
    wb
    @32
    @7
    cK
    clat
    wcel
    #
    @3
    @8
    cB
    wcel
    #
    @40
    @7
    @0
    @42
    @27
    cK
    hllat
    syl
    #
    @33
    @7
    @42
    @4
    @35
    @43
    @44
    @34
    @36
    cB
    cK
    c.an
    cY
    cW
    lhpmod.b
    lhpmod.m
    latmcl
    syl3anc
    #
    cB
    c.or
    cK
    cX
    @8
    lhpmod.b
    lhpmod.j
    latjcl
    syl3anc
    @7
    @42
    @10
    cB
    wcel
    #
    @35
    @41
    @44
    @7
    @42
    @3
    @4
    @46
    @44
    @33
    @34
    cB
    c.or
    cK
    cX
    cY
    lhpmod.b
    lhpmod.j
    latjcl
    syl3anc
    #
    @36
    cB
    cK
    c.an
    @10
    cW
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
    @37
    @18
    @38
    @20
    @7
    @37
    @10
    @13
    cfv
    #
    @17
    c.or
    co
    #
    @18
    @7
    cK
    col
    wcel
    #
    @46
    @35
    @37
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
    @47
    @36
    cB
    c.or
    cK
    c.an
    @13
    @10
    cW
    lhpmod.b
    lhpmod.j
    lhpmod.m
    @29
    oldmm1
    syl3anc
    @7
    @48
    @16
    @17
    c.or
    @7
    @50
    @3
    @4
    @48
    @16
    wceq
    @51
    @33
    @34
    cB
    c.or
    cK
    c.an
    @13
    cX
    cY
    lhpmod.b
    lhpmod.j
    lhpmod.m
    @29
    oldmj1
    syl3anc
    oveq1d
    eqtrd
    @7
    @38
    @14
    @8
    @13
    cfv
    #
    c.an
    co
    #
    @20
    @7
    @50
    @3
    @43
    @38
    @53
    wceq
    @51
    @33
    @45
    cB
    c.or
    cK
    c.an
    @13
    cX
    @8
    lhpmod.b
    lhpmod.j
    lhpmod.m
    @29
    oldmj1
    syl3anc
    @7
    @52
    @19
    @14
    c.an
    @7
    @50
    @4
    @35
    @52
    @19
    wceq
    @51
    @34
    @36
    cB
    c.or
    cK
    c.an
    @13
    cY
    cW
    lhpmod.b
    lhpmod.j
    lhpmod.m
    @29
    oldmm1
    syl3anc
    oveq2d
    eqtrd
    eqeq12d
    bitrd
    mpbird
end
