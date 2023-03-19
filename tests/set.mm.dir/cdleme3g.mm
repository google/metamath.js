include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cdleme3d.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp23l.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22l.mm"
include "simp3l.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp3r.mm"
include "jca.mm"
include "cdleme3e.mm"
include "syl13anc.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp22r.mm"
include "wi.mm"
include "simp23.mm"
include "simp3.mm"
include "cdleme0e.mm"
include "syl131anc.mm"
include "hlatexch2.mm"
include "simp21l.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "wb.mm"
include "atbase.mm"
include "latjle12.mm"
include "mpbi2and.mm"
include "lattr.mm"
include "mpan2d.mm"
include "syld.mm"
include "mtod.mm"
include "nbrne2.mm"
include "syl2anc.mm"

theorem cdleme3g
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
  let cV: class V
  let cW: class W
  assume cdleme1.l: |- .<_ = ( le ` K )
  assume cdleme1.j: |- .\/ = ( join ` K )
  assume cdleme1.m: |- ./\ = ( meet ` K )
  assume cdleme1.a: |- A = ( Atoms ` K )
  assume cdleme1.h: |- H = ( LHyp ` K )
  assume cdleme1.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme1.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )
  assume cdleme3.3: |- V = ( ( P .\/ R ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( P =/= Q /\ -. R .<_ ( P .\/ Q ) ) ) -> F =/= U )

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
    #
    wn
    #
    wa
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
    cP
    cQ
    wne
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
    wa
    #
    w3a
    #
    cF
    cQ
    cV
    c.or
    co
    #
    c.le
    wbr
    cU
    @19
    c.le
    wbr
    #
    wn
    cF
    cU
    wne
    @18
    cF
    cR
    cU
    c.or
    co
    #
    @19
    c.an
    co
    #
    @19
    c.le
    cA
    cP
    cQ
    cR
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    cdleme1.f
    cdleme3.3
    cdleme3d
    @18
    cK
    clat
    wcel
    #
    @21
    cK
    cbs
    cfv
    #
    wcel
    #
    @19
    @24
    wcel
    #
    @22
    @19
    c.le
    wbr
    @18
    @0
    @23
    @0
    @1
    @13
    @17
    simp1l
    #
    cK
    hllat
    syl
    #
    @18
    @0
    @10
    cU
    cA
    wcel
    #
    @25
    @27
    @10
    @11
    @5
    @9
    @2
    @17
    simp23l
    #
    @18
    @2
    @5
    @6
    @14
    @29
    @2
    @13
    @17
    simp1
    #
    @2
    @5
    @9
    @12
    @17
    simp21
    #
    @6
    @8
    @5
    @12
    @2
    @17
    simp22l
    #
    @2
    @13
    @14
    @16
    simp3l
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
    lhpat2
    syl112anc
    #
    cA
    @24
    c.or
    cK
    cR
    cU
    @24
    eqid
    #
    cdleme1.j
    cdleme1.a
    hlatjcl
    syl3anc
    @18
    @0
    @6
    cV
    cA
    wcel
    #
    @26
    @27
    @33
    @18
    @2
    @5
    @6
    @10
    @16
    wa
    @36
    @31
    @32
    @33
    @18
    @10
    @16
    @30
    @2
    @13
    @14
    @16
    simp3r
    jca
    cA
    cP
    cQ
    cR
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    cdleme1.f
    cdleme3.3
    cdleme3e
    syl13anc
    #
    cA
    @24
    c.or
    cK
    cQ
    cV
    @35
    cdleme1.j
    cdleme1.a
    hlatjcl
    syl3anc
    @24
    cK
    c.le
    c.an
    @21
    @19
    @35
    cdleme1.l
    cdleme1.m
    latmle2
    syl3anc
    syl5eqbr
    @18
    @20
    @7
    @6
    @8
    @5
    @12
    @2
    @17
    simp22r
    @18
    @20
    cQ
    cU
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    @7
    @18
    @0
    @29
    @6
    @36
    cU
    cV
    wne
    #
    @20
    @39
    wi
    @27
    @34
    @33
    @37
    @18
    @2
    @5
    @6
    @12
    @17
    @40
    @31
    @32
    @33
    @2
    @5
    @9
    @12
    @17
    simp23
    @2
    @13
    @17
    simp3
    cA
    cP
    cQ
    cR
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    cdleme3.3
    cdleme0e
    syl131anc
    cA
    cU
    cQ
    cV
    c.or
    cK
    c.le
    cdleme1.l
    cdleme1.j
    cdleme1.a
    hlatexch2
    syl131anc
    @18
    @39
    @38
    cW
    c.le
    wbr
    #
    @7
    @18
    cU
    cW
    c.le
    wbr
    #
    cV
    cW
    c.le
    wbr
    #
    @41
    @18
    cU
    @15
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme1.u
    @18
    @23
    @15
    @24
    wcel
    #
    cW
    @24
    wcel
    #
    @44
    cW
    c.le
    wbr
    @28
    @18
    @0
    @3
    @6
    @45
    @27
    @3
    @4
    @9
    @12
    @2
    @17
    simp21l
    #
    @33
    cA
    @24
    c.or
    cK
    cP
    cQ
    @35
    cdleme1.j
    cdleme1.a
    hlatjcl
    syl3anc
    @18
    @1
    @46
    @0
    @1
    @13
    @17
    simp1r
    @24
    cH
    cK
    cW
    @35
    cdleme1.h
    lhpbase
    syl
    #
    @24
    cK
    c.le
    c.an
    @15
    cW
    @35
    cdleme1.l
    cdleme1.m
    latmle2
    syl3anc
    syl5eqbr
    @18
    cV
    cP
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme3.3
    @18
    @23
    @49
    @24
    wcel
    #
    @46
    @50
    cW
    c.le
    wbr
    @28
    @18
    @0
    @3
    @10
    @51
    @27
    @47
    @30
    cA
    @24
    c.or
    cK
    cP
    cR
    @35
    cdleme1.j
    cdleme1.a
    hlatjcl
    syl3anc
    @48
    @24
    cK
    c.le
    c.an
    @49
    cW
    @35
    cdleme1.l
    cdleme1.m
    latmle2
    syl3anc
    syl5eqbr
    @18
    @23
    cU
    @24
    wcel
    #
    cV
    @24
    wcel
    #
    @46
    @42
    @43
    wa
    @41
    wb
    @28
    @18
    @29
    @52
    @34
    cA
    @24
    cU
    cK
    @35
    cdleme1.a
    atbase
    syl
    @18
    @36
    @53
    @37
    cA
    @24
    cV
    cK
    @35
    cdleme1.a
    atbase
    syl
    @48
    @24
    c.or
    cK
    c.le
    cU
    cV
    cW
    @35
    cdleme1.l
    cdleme1.j
    latjle12
    syl13anc
    mpbi2and
    @18
    @23
    cQ
    @24
    wcel
    #
    @38
    @24
    wcel
    #
    @46
    @39
    @41
    wa
    @7
    wi
    @28
    @18
    @6
    @54
    @33
    cA
    @24
    cQ
    cK
    @35
    cdleme1.a
    atbase
    syl
    @18
    @0
    @29
    @36
    @55
    @27
    @34
    @37
    cA
    @24
    c.or
    cK
    cU
    cV
    @35
    cdleme1.j
    cdleme1.a
    hlatjcl
    syl3anc
    @48
    @24
    cK
    c.le
    cQ
    @38
    cW
    @35
    cdleme1.l
    lattr
    syl13anc
    mpan2d
    syld
    mtod
    cF
    cU
    @19
    c.le
    nbrne2
    syl2anc
end
