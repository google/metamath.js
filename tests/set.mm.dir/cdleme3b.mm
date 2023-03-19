include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "ccvr.mm"
include "simpll.mm"
include "simpr3l.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "lhpat2.mm"
include "3adant3r3.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simpr2l.mm"
include "simpr1l.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latmcl.mm"
include "syl5eqel.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simpr3r.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "necomd.mm"
include "wb.mm"
include "atcvr1.mm"
include "mpbid.mm"
include "wceq.mm"
include "simpr3.mm"
include "3jca.mm"
include "cdleme1.mm"
include "syldan.mm"
include "breqtrrd.mm"
include "cvrne.mm"
include "syl31anc.mm"
include "oveq2.mm"
include "adantl.mm"
include "hlatjidm.mm"
include "adantr.mm"
include "eqtr2d.mm"
include "ex.mm"
include "necon3d.mm"
include "mpd.mm"

theorem cdleme3b
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ P =/= Q ) /\ ( R e. A /\ -. R .<_ W ) ) ) -> F =/= R )

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
    cP
    cQ
    wne
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
    wa
    #
    cR
    cR
    cF
    c.or
    co
    #
    wne
    #
    cF
    cR
    wne
    @13
    @0
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    @14
    @16
    wcel
    #
    cR
    @14
    cK
    ccvr
    cfv
    #
    wbr
    @15
    @0
    @1
    @12
    simpll
    #
    @13
    @9
    @17
    @9
    @10
    @5
    @8
    @2
    simpr3l
    #
    cA
    @16
    cR
    cK
    @16
    eqid
    #
    cdleme1.a
    atbase
    syl
    #
    @13
    cK
    clat
    wcel
    #
    @17
    cF
    @16
    wcel
    @18
    @0
    @24
    @1
    @12
    cK
    hllat
    ad2antrr
    #
    @23
    @13
    cF
    cR
    cU
    c.or
    co
    #
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
    @16
    cdleme1.f
    @13
    @24
    @26
    @16
    wcel
    #
    @29
    @16
    wcel
    #
    @30
    @16
    wcel
    @25
    @13
    @24
    @17
    cU
    @16
    wcel
    #
    @31
    @25
    @23
    @13
    cU
    cA
    wcel
    #
    @33
    @2
    @5
    @8
    @34
    @11
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
    3adant3r3
    #
    cA
    @16
    cU
    cK
    @22
    cdleme1.a
    atbase
    syl
    @16
    c.or
    cK
    cR
    cU
    @22
    cdleme1.j
    latjcl
    syl3anc
    @13
    @24
    cQ
    @16
    wcel
    #
    @28
    @16
    wcel
    #
    @32
    @25
    @13
    @6
    @36
    @6
    @7
    @5
    @11
    @2
    simpr2l
    #
    cA
    @16
    cQ
    cK
    @22
    cdleme1.a
    atbase
    syl
    #
    @13
    @24
    @27
    @16
    wcel
    #
    cW
    @16
    wcel
    #
    @37
    @25
    @13
    @24
    cP
    @16
    wcel
    #
    @17
    @40
    @25
    @13
    @3
    @42
    @3
    @4
    @8
    @11
    @2
    simpr1l
    #
    cA
    @16
    cP
    cK
    @22
    cdleme1.a
    atbase
    syl
    #
    @23
    @16
    c.or
    cK
    cP
    cR
    @22
    cdleme1.j
    latjcl
    syl3anc
    @1
    @41
    @0
    @12
    @16
    cH
    cK
    cW
    @22
    cdleme1.h
    lhpbase
    ad2antlr
    #
    @16
    cK
    c.an
    @27
    cW
    @22
    cdleme1.m
    latmcl
    syl3anc
    @16
    c.or
    cK
    cQ
    @28
    @22
    cdleme1.j
    latjcl
    syl3anc
    @16
    cK
    c.an
    @26
    @29
    @22
    cdleme1.m
    latmcl
    syl3anc
    syl5eqel
    @16
    c.or
    cK
    cR
    cF
    @22
    cdleme1.j
    latjcl
    syl3anc
    @13
    cR
    @26
    @14
    @19
    @13
    cR
    cU
    wne
    #
    cR
    @26
    @19
    wbr
    #
    @13
    cU
    cR
    @13
    cU
    cW
    c.le
    wbr
    @10
    cU
    cR
    wne
    @13
    cU
    cP
    cQ
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme1.u
    @13
    @24
    @48
    @16
    wcel
    #
    @41
    @49
    cW
    c.le
    wbr
    @25
    @13
    @24
    @42
    @36
    @50
    @25
    @44
    @39
    @16
    c.or
    cK
    cP
    cQ
    @22
    cdleme1.j
    latjcl
    syl3anc
    @45
    @16
    cK
    c.le
    c.an
    @48
    cW
    @22
    cdleme1.l
    cdleme1.m
    latmle2
    syl3anc
    syl5eqbr
    @9
    @10
    @5
    @8
    @2
    simpr3r
    cU
    cR
    cW
    c.le
    nbrne2
    syl2anc
    necomd
    @13
    @0
    @9
    @34
    @46
    @47
    wb
    @20
    @21
    @35
    cA
    @19
    cR
    cU
    c.or
    cK
    cdleme1.j
    @19
    eqid
    #
    cdleme1.a
    atcvr1
    syl3anc
    mpbid
    @2
    @12
    @3
    @6
    @11
    w3a
    @14
    @26
    wceq
    @13
    @3
    @6
    @11
    @43
    @38
    @2
    @5
    @8
    @11
    simpr3
    3jca
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
    cW
    cdleme1.l
    cdleme1.j
    cdleme1.m
    cdleme1.a
    cdleme1.h
    cdleme1.u
    cdleme1.f
    cdleme1
    syldan
    breqtrrd
    chlt
    @16
    @19
    cK
    cR
    @14
    @22
    @51
    cvrne
    syl31anc
    @13
    cF
    cR
    cR
    @14
    @13
    cF
    cR
    wceq
    #
    cR
    @14
    wceq
    @13
    @52
    wa
    @14
    cR
    cR
    c.or
    co
    #
    cR
    @52
    @14
    @53
    wceq
    @13
    cF
    cR
    cR
    c.or
    oveq2
    adantl
    @13
    @53
    cR
    wceq
    #
    @52
    @13
    @0
    @9
    @54
    @20
    @21
    cA
    c.or
    cK
    cR
    cdleme1.j
    cdleme1.a
    hlatjidm
    syl2anc
    adantr
    eqtr2d
    ex
    necon3d
    mpd
end
