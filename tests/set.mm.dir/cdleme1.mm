include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simpll.mm"
include "simpr3l.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "latlej1.mm"
include "atmod3i1.mm"
include "syl131anc.mm"
include "cp1.mm"
include "latlej2.mm"
include "lhpjat2.mm"
include "3ad2antr3.mm"
include "oveq2d.mm"
include "col.mm"
include "hlol.mm"
include "olm11.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "latj12.mm"
include "syl13anc.mm"
include "latj13.mm"
include "3eqtr3rd.mm"
include "cdlemeulpq.mm"
include "3adantr3.mm"
include "wi.mm"
include "latjlej2.mm"
include "mpd.mm"
include "wb.mm"
include "latleeqm1.mm"
include "mpbid.mm"
include "3eqtr2rd.mm"
include "oveq2i.mm"
include "syl6reqr.mm"

theorem cdleme1
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
  assume cdleme1.l: |- .<_ = ( le ` K )
  assume cdleme1.j: |- .\/ = ( join ` K )
  assume cdleme1.m: |- ./\ = ( meet ` K )
  assume cdleme1.a: |- A = ( Atoms ` K )
  assume cdleme1.h: |- H = ( LHyp ` K )
  assume cdleme1.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme1.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A /\ ( R e. A /\ -. R .<_ W ) ) ) -> ( R .\/ F ) = ( R .\/ U ) )

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
    cQ
    cA
    wcel
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
    w3a
    #
    wa
    #
    cR
    cU
    c.or
    co
    #
    cR
    @10
    cQ
    cP
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    c.or
    co
    #
    cR
    cF
    c.or
    co
    @9
    @15
    @10
    cR
    @13
    c.or
    co
    #
    c.an
    co
    #
    @10
    cR
    cP
    cQ
    c.or
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    @10
    @9
    @0
    @5
    @10
    cK
    cbs
    cfv
    #
    wcel
    #
    @13
    @21
    wcel
    #
    cR
    @10
    c.le
    wbr
    #
    @15
    @17
    wceq
    @0
    @1
    @8
    simpll
    #
    @5
    @6
    @3
    @4
    @2
    simpr3l
    #
    @9
    cK
    clat
    wcel
    #
    cR
    @21
    wcel
    #
    cU
    @21
    wcel
    #
    @22
    @0
    @27
    @1
    @8
    cK
    hllat
    ad2antrr
    #
    @9
    @5
    @28
    @26
    cA
    @21
    cR
    cK
    @21
    eqid
    #
    cdleme1.a
    atbase
    syl
    #
    @9
    cU
    @18
    cW
    c.an
    co
    #
    @21
    cdleme1.u
    @9
    @27
    @18
    @21
    wcel
    #
    cW
    @21
    wcel
    #
    @33
    @21
    wcel
    @30
    @9
    @27
    cP
    @21
    wcel
    #
    cQ
    @21
    wcel
    #
    @34
    @30
    @9
    @3
    @36
    @2
    @3
    @4
    @7
    simpr1
    cA
    @21
    cP
    cK
    @31
    cdleme1.a
    atbase
    syl
    #
    @9
    @4
    @37
    @2
    @3
    @4
    @7
    simpr2
    cA
    @21
    cQ
    cK
    @31
    cdleme1.a
    atbase
    syl
    #
    @21
    c.or
    cK
    cP
    cQ
    @31
    cdleme1.j
    latjcl
    syl3anc
    #
    @1
    @35
    @0
    @8
    @21
    cH
    cK
    cW
    @31
    cdleme1.h
    lhpbase
    ad2antlr
    #
    @21
    cK
    c.an
    @18
    cW
    @31
    cdleme1.m
    latmcl
    syl3anc
    syl5eqel
    #
    @21
    c.or
    cK
    cR
    cU
    @31
    cdleme1.j
    latjcl
    syl3anc
    #
    @9
    @27
    @37
    @12
    @21
    wcel
    #
    @23
    @30
    @39
    @9
    @27
    @11
    @21
    wcel
    #
    @35
    @44
    @30
    @9
    @27
    @36
    @28
    @45
    @30
    @38
    @32
    @21
    c.or
    cK
    cP
    cR
    @31
    cdleme1.j
    latjcl
    syl3anc
    #
    @41
    @21
    cK
    c.an
    @11
    cW
    @31
    cdleme1.m
    latmcl
    syl3anc
    #
    @21
    c.or
    cK
    cQ
    @12
    @31
    cdleme1.j
    latjcl
    syl3anc
    @9
    @27
    @28
    @29
    @24
    @30
    @32
    @42
    @21
    c.or
    cK
    c.le
    cR
    cU
    @31
    cdleme1.l
    cdleme1.j
    latlej1
    syl3anc
    cA
    @21
    cR
    c.or
    cK
    c.le
    c.an
    @10
    @13
    @31
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    atmod3i1
    syl131anc
    @9
    @19
    @16
    @10
    c.an
    @9
    cQ
    cR
    @12
    c.or
    co
    #
    c.or
    co
    #
    cQ
    @11
    c.or
    co
    #
    @16
    @19
    @9
    @48
    @11
    cQ
    c.or
    @9
    @48
    @11
    cR
    cW
    c.or
    co
    #
    c.an
    co
    #
    @11
    cK
    cp1
    cfv
    #
    c.an
    co
    #
    @11
    @9
    @0
    @5
    @45
    @35
    cR
    @11
    c.le
    wbr
    #
    @48
    @52
    wceq
    @25
    @26
    @46
    @41
    @9
    @27
    @36
    @28
    @55
    @30
    @38
    @32
    @21
    c.or
    cK
    c.le
    cP
    cR
    @31
    cdleme1.l
    cdleme1.j
    latlej2
    syl3anc
    cA
    @21
    cR
    c.or
    cK
    c.le
    c.an
    @11
    cW
    @31
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    atmod3i1
    syl131anc
    @9
    @51
    @53
    @11
    c.an
    @2
    @3
    @7
    @51
    @53
    wceq
    @4
    cA
    cR
    @53
    cH
    c.or
    cK
    c.le
    cW
    cdleme1.l
    cdleme1.j
    @53
    eqid
    #
    cdleme1.a
    cdleme1.h
    lhpjat2
    3ad2antr3
    oveq2d
    @9
    cK
    col
    wcel
    #
    @45
    @54
    @11
    wceq
    @0
    @57
    @1
    @8
    cK
    hlol
    ad2antrr
    @46
    @21
    @53
    cK
    c.an
    @11
    @31
    cdleme1.m
    @56
    olm11
    syl2anc
    3eqtrd
    oveq2d
    @9
    @27
    @37
    @28
    @44
    @49
    @16
    wceq
    @30
    @39
    @32
    @47
    @21
    c.or
    cK
    cQ
    cR
    @12
    @31
    cdleme1.j
    latj12
    syl13anc
    @9
    @27
    @37
    @36
    @28
    @50
    @19
    wceq
    @30
    @39
    @38
    @32
    @21
    c.or
    cK
    cQ
    cP
    cR
    @31
    cdleme1.j
    latj13
    syl13anc
    3eqtr3rd
    oveq2d
    @9
    @10
    @19
    c.le
    wbr
    #
    @20
    @10
    wceq
    #
    @9
    cU
    @18
    c.le
    wbr
    #
    @58
    @2
    @3
    @4
    @60
    @7
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
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    cdlemeulpq
    3adantr3
    @9
    @27
    @29
    @34
    @28
    @60
    @58
    wi
    @30
    @42
    @40
    @32
    @21
    c.or
    cK
    c.le
    cU
    @18
    cR
    @31
    cdleme1.l
    cdleme1.j
    latjlej2
    syl13anc
    mpd
    @9
    @27
    @22
    @19
    @21
    wcel
    #
    @58
    @59
    wb
    @30
    @43
    @9
    @27
    @28
    @34
    @61
    @30
    @32
    @40
    @21
    c.or
    cK
    cR
    @18
    @31
    cdleme1.j
    latjcl
    syl3anc
    @21
    cK
    c.le
    c.an
    @10
    @19
    @31
    cdleme1.l
    cdleme1.m
    latleeqm1
    syl3anc
    mpbid
    3eqtr2rd
    cF
    @14
    cR
    c.or
    cdleme1.f
    oveq2i
    syl6reqr
end
