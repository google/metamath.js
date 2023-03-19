include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "simp3r.mm"
include "simp1l.mm"
include "simp22l.mm"
include "simp23l.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "eqid.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "wi.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmlem1.mm"
include "mpd.mm"
include "cp0.mm"
include "simp1.mm"
include "simp22.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "simp23r.mm"
include "atmod4i1.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "3eqtr3d.mm"
include "breqtrd.mm"
include "cal.mm"
include "hlatl.mm"
include "simp21r.mm"
include "simp3l.mm"
include "lhpat.mm"
include "syl222anc.mm"
include "atcmp.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem cdleme22d
  let cA: class A
  let cS: class S
  let cT: class T
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme22.l: |- .<_ = ( le ` K )
  assume cdleme22.j: |- .\/ = ( join ` K )
  assume cdleme22.m: |- ./\ = ( meet ` K )
  assume cdleme22.a: |- A = ( Atoms ` K )
  assume cdleme22.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( V e. A /\ V .<_ W ) ) /\ ( S =/= T /\ S .<_ ( T .\/ V ) ) ) -> V = ( ( S .\/ T ) ./\ W ) )

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
    cT
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cS
    cT
    wne
    #
    cS
    cT
    cV
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
    cS
    cT
    c.or
    co
    #
    cW
    c.an
    co
    #
    cV
    @17
    @19
    cV
    c.le
    wbr
    #
    @19
    cV
    wceq
    #
    @17
    @19
    @14
    cW
    c.an
    co
    #
    cV
    c.le
    @17
    @18
    @14
    c.le
    wbr
    #
    @19
    @22
    c.le
    wbr
    #
    @17
    @15
    cT
    @14
    c.le
    wbr
    #
    @23
    @2
    @12
    @13
    @15
    simp3r
    @17
    @0
    @6
    @9
    @25
    @0
    @1
    @12
    @16
    simp1l
    #
    @6
    @7
    @5
    @11
    @2
    @16
    simp22l
    #
    @9
    @10
    @5
    @8
    @2
    @16
    simp23l
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
    @17
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
    @30
    wcel
    #
    @14
    @30
    wcel
    #
    @15
    @25
    wa
    @23
    wb
    @17
    @0
    @29
    @26
    cK
    hllat
    syl
    #
    @17
    @3
    @31
    @3
    @4
    @8
    @11
    @2
    @16
    simp21l
    #
    cA
    @30
    cS
    cK
    @30
    eqid
    #
    cdleme22.a
    atbase
    syl
    @17
    @6
    @32
    @27
    cA
    @30
    cT
    cK
    @36
    cdleme22.a
    atbase
    syl
    #
    @17
    @0
    @6
    @9
    @33
    @26
    @27
    @28
    cA
    @30
    c.or
    cK
    cT
    cV
    @36
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    #
    @30
    c.or
    cK
    c.le
    cS
    cT
    @14
    @36
    cdleme22.l
    cdleme22.j
    latjle12
    syl13anc
    mpbi2and
    @17
    @29
    @18
    @30
    wcel
    #
    @33
    cW
    @30
    wcel
    #
    @23
    @24
    wi
    @34
    @17
    @0
    @3
    @6
    @39
    @26
    @35
    @27
    cA
    @30
    c.or
    cK
    cS
    cT
    @36
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    @38
    @17
    @1
    @40
    @0
    @1
    @12
    @16
    simp1r
    #
    @30
    cH
    cK
    cW
    @36
    cdleme22.h
    lhpbase
    syl
    #
    @30
    cK
    c.le
    c.an
    @18
    @14
    cW
    @36
    cdleme22.l
    cdleme22.m
    latmlem1
    syl13anc
    mpd
    @17
    cT
    cW
    c.an
    co
    #
    cV
    c.or
    co
    #
    cK
    cp0
    cfv
    #
    cV
    c.or
    co
    #
    @22
    cV
    @17
    @43
    @45
    cV
    c.or
    @17
    @2
    @8
    @43
    @45
    wceq
    @2
    @12
    @16
    simp1
    @2
    @5
    @8
    @11
    @16
    simp22
    cA
    cT
    cH
    cK
    c.le
    c.an
    cW
    @45
    cdleme22.l
    cdleme22.m
    @45
    eqid
    #
    cdleme22.a
    cdleme22.h
    lhpmat
    syl2anc
    oveq1d
    @17
    @0
    @9
    @32
    @40
    @10
    @44
    @22
    wceq
    @26
    @28
    @37
    @42
    @9
    @10
    @5
    @8
    @2
    @16
    simp23r
    cA
    @30
    cV
    c.or
    cK
    c.le
    c.an
    cT
    cW
    @36
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    atmod4i1
    syl131anc
    @17
    cK
    col
    wcel
    #
    cV
    @30
    wcel
    #
    @46
    cV
    wceq
    @17
    @0
    @48
    @26
    cK
    hlol
    syl
    @17
    @9
    @49
    @28
    cA
    @30
    cV
    cK
    @36
    cdleme22.a
    atbase
    syl
    @30
    c.or
    cK
    cV
    @45
    @36
    cdleme22.j
    @47
    olj02
    syl2anc
    3eqtr3d
    breqtrd
    @17
    cK
    cal
    wcel
    #
    @19
    cA
    wcel
    #
    @9
    @20
    @21
    wb
    @17
    @0
    @50
    @26
    cK
    hlatl
    syl
    @17
    @0
    @1
    @3
    @4
    @6
    @13
    @51
    @26
    @41
    @35
    @3
    @4
    @8
    @11
    @2
    @16
    simp21r
    @27
    @2
    @12
    @13
    @15
    simp3l
    cA
    cS
    cT
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    lhpat
    syl222anc
    @28
    cA
    @19
    cV
    cK
    c.le
    cdleme22.l
    cdleme22.a
    atcmp
    syl3anc
    mpbid
    eqcomd
end
