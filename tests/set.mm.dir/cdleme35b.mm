include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp13l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp2rl.mm"
include "simp11.mm"
include "simp12.mm"
include "simp2l.mm"
include "cdleme0a.mm"
include "syl112anc.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "latlej1.mm"
include "simp12l.mm"
include "latjcl.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latmle1.mm"
include "lattrd.mm"
include "oveq2i.mm"
include "cp1.mm"
include "wceq.mm"
include "hlatlej2.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "simp13.mm"
include "lhpjat2.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "3eqtrd.mm"
include "syl5eq.mm"
include "hlatj12.mm"
include "syl13anc.mm"
include "hlatjcom.mm"
include "oveq1d.mm"
include "hlatjass.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"
include "breqtrd.mm"
include "wb.mm"
include "latjle12.mm"
include "mpbi2and.mm"

theorem cdleme35b
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme35.l: |- .<_ = ( le ` K )
  assume cdleme35.j: |- .\/ = ( join ` K )
  assume cdleme35.m: |- ./\ = ( meet ` K )
  assume cdleme35.a: |- A = ( Atoms ` K )
  assume cdleme35.h: |- H = ( LHyp ` K )
  assume cdleme35.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme35.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> ( Q .\/ ( ( P .\/ R ) ./\ W ) ) .<_ ( Q .\/ ( R .\/ U ) ) )

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
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    cQ
    cQ
    cR
    cU
    c.or
    co
    #
    c.or
    co
    #
    c.le
    wbr
    #
    cP
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    @19
    c.le
    wbr
    #
    cQ
    @22
    c.or
    co
    @19
    c.le
    wbr
    #
    @17
    cK
    clat
    wcel
    #
    cQ
    cK
    cbs
    cfv
    #
    wcel
    #
    @18
    @26
    wcel
    #
    @20
    @17
    @0
    @25
    @0
    @1
    @5
    @8
    @14
    @16
    simp11l
    #
    cK
    hllat
    syl
    #
    @17
    @6
    @27
    @6
    @7
    @2
    @5
    @14
    @16
    simp13l
    #
    cA
    @26
    cQ
    cK
    @26
    eqid
    #
    cdleme35.a
    atbase
    syl
    #
    @17
    @0
    @11
    cU
    cA
    wcel
    #
    @28
    @29
    @11
    @12
    @10
    @9
    @16
    simp2rl
    #
    @17
    @2
    @5
    @6
    @10
    @34
    @2
    @5
    @8
    @14
    @16
    simp11
    #
    @2
    @5
    @8
    @14
    @16
    simp12
    @31
    @9
    @10
    @13
    @16
    simp2l
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
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    cdleme35.h
    cdleme35.u
    cdleme0a
    syl112anc
    #
    cA
    @26
    c.or
    cK
    cR
    cU
    @32
    cdleme35.j
    cdleme35.a
    hlatjcl
    syl3anc
    #
    @26
    c.or
    cK
    c.le
    cQ
    @18
    @32
    cdleme35.l
    cdleme35.j
    latlej1
    syl3anc
    @17
    @22
    @21
    cQ
    c.or
    co
    #
    @19
    c.le
    @17
    @26
    cK
    c.le
    @22
    @21
    @39
    @32
    cdleme35.l
    @30
    @17
    @25
    @21
    @26
    wcel
    #
    cW
    @26
    wcel
    #
    @22
    @26
    wcel
    #
    @30
    @17
    @25
    cP
    @26
    wcel
    #
    cR
    @26
    wcel
    #
    @40
    @30
    @17
    @3
    @43
    @3
    @4
    @2
    @8
    @14
    @16
    simp12l
    #
    cA
    @26
    cP
    cK
    @32
    cdleme35.a
    atbase
    syl
    @17
    @11
    @44
    @35
    cA
    @26
    cR
    cK
    @32
    cdleme35.a
    atbase
    syl
    @26
    c.or
    cK
    cP
    cR
    @32
    cdleme35.j
    latjcl
    syl3anc
    #
    @17
    @1
    @41
    @0
    @1
    @5
    @8
    @14
    @16
    simp11r
    @26
    cH
    cK
    cW
    @32
    cdleme35.h
    lhpbase
    syl
    #
    @26
    cK
    c.an
    @21
    cW
    @32
    cdleme35.m
    latmcl
    syl3anc
    #
    @46
    @17
    @25
    @40
    @27
    @39
    @26
    wcel
    @30
    @46
    @33
    @26
    c.or
    cK
    @21
    cQ
    @32
    cdleme35.j
    latjcl
    syl3anc
    @17
    @25
    @40
    @41
    @22
    @21
    c.le
    wbr
    @30
    @46
    @47
    @26
    cK
    c.le
    c.an
    @21
    cW
    @32
    cdleme35.l
    cdleme35.m
    latmle1
    syl3anc
    @17
    @25
    @40
    @27
    @21
    @39
    c.le
    wbr
    @30
    @46
    @33
    @26
    c.or
    cK
    c.le
    @21
    cQ
    @32
    cdleme35.l
    cdleme35.j
    latlej1
    syl3anc
    lattrd
    @17
    cR
    cQ
    cU
    c.or
    co
    #
    c.or
    co
    #
    cR
    @15
    c.or
    co
    #
    @19
    @39
    @17
    @49
    @15
    cR
    c.or
    @17
    @49
    cQ
    @15
    cW
    c.an
    co
    #
    c.or
    co
    #
    @15
    cU
    @52
    cQ
    c.or
    cdleme35.u
    oveq2i
    @17
    @53
    @15
    cQ
    cW
    c.or
    co
    #
    c.an
    co
    #
    @15
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @15
    @17
    @0
    @6
    @15
    @26
    wcel
    #
    @41
    cQ
    @15
    c.le
    wbr
    #
    @53
    @55
    wceq
    @29
    @31
    @17
    @0
    @3
    @6
    @58
    @29
    @45
    @31
    cA
    @26
    c.or
    cK
    cP
    cQ
    @32
    cdleme35.j
    cdleme35.a
    hlatjcl
    syl3anc
    #
    @47
    @17
    @0
    @3
    @6
    @59
    @29
    @45
    @31
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdleme35.l
    cdleme35.j
    cdleme35.a
    hlatlej2
    syl3anc
    cA
    @26
    cQ
    c.or
    cK
    c.le
    c.an
    @15
    cW
    @32
    cdleme35.l
    cdleme35.j
    cdleme35.m
    cdleme35.a
    atmod3i1
    syl131anc
    @17
    @54
    @56
    @15
    c.an
    @17
    @2
    @8
    @54
    @56
    wceq
    @36
    @2
    @5
    @8
    @14
    @16
    simp13
    cA
    cQ
    @56
    cH
    c.or
    cK
    c.le
    cW
    cdleme35.l
    cdleme35.j
    @56
    eqid
    #
    cdleme35.a
    cdleme35.h
    lhpjat2
    syl2anc
    oveq2d
    @17
    cK
    col
    wcel
    #
    @58
    @57
    @15
    wceq
    @17
    @0
    @62
    @29
    cK
    hlol
    syl
    @60
    @26
    @56
    cK
    c.an
    @15
    @32
    cdleme35.m
    @61
    olm11
    syl2anc
    3eqtrd
    syl5eq
    oveq2d
    @17
    @0
    @6
    @11
    @34
    @19
    @50
    wceq
    @29
    @31
    @35
    @37
    cA
    cQ
    cR
    cU
    c.or
    cK
    cdleme35.j
    cdleme35.a
    hlatj12
    syl13anc
    @17
    @39
    cR
    cP
    c.or
    co
    #
    cQ
    c.or
    co
    #
    @51
    @17
    @21
    @63
    cQ
    c.or
    @17
    @0
    @3
    @11
    @21
    @63
    wceq
    @29
    @45
    @35
    cA
    c.or
    cK
    cP
    cR
    cdleme35.j
    cdleme35.a
    hlatjcom
    syl3anc
    oveq1d
    @17
    @0
    @11
    @3
    @6
    @64
    @51
    wceq
    @29
    @35
    @45
    @31
    cA
    cR
    cP
    cQ
    c.or
    cK
    cdleme35.j
    cdleme35.a
    hlatjass
    syl13anc
    eqtrd
    3eqtr4rd
    breqtrd
    @17
    @25
    @27
    @42
    @19
    @26
    wcel
    #
    @20
    @23
    wa
    @24
    wb
    @30
    @33
    @48
    @17
    @25
    @27
    @28
    @65
    @30
    @33
    @38
    @26
    c.or
    cK
    cQ
    @18
    @32
    cdleme35.j
    latjcl
    syl3anc
    @26
    c.or
    cK
    c.le
    cQ
    @22
    @19
    @32
    cdleme35.l
    cdleme35.j
    latjle12
    syl13anc
    mpbi2and
end
