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
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "simpr3l.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "cops.mm"
include "hlop.mm"
include "op0cl.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simpl.mm"
include "simpr1l.mm"
include "simpr2l.mm"
include "cdleme1b.mm"
include "syl13anc.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simpr3r.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "necomd.mm"
include "wb.mm"
include "lhpat2.mm"
include "3adant3r3.mm"
include "atcvr1.mm"
include "mpbid.mm"
include "col.mm"
include "wceq.mm"
include "hlol.mm"
include "olj01.mm"
include "simpr3.mm"
include "cdleme1.mm"
include "3brtr4d.mm"
include "cvrne.mm"
include "syl31anc.mm"
include "oveq2.mm"
include "necon3i.mm"

theorem cdleme3c
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
  let c.0: class .0.
  assume cdleme1.l: |- .<_ = ( le ` K )
  assume cdleme1.j: |- .\/ = ( join ` K )
  assume cdleme1.m: |- ./\ = ( meet ` K )
  assume cdleme1.a: |- A = ( Atoms ` K )
  assume cdleme1.h: |- H = ( LHyp ` K )
  assume cdleme1.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme1.f: |- F = ( ( R .\/ U ) ./\ ( Q .\/ ( ( P .\/ R ) ./\ W ) ) )
  assume cdleme3c.z: |- .0. = ( 0. ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ P =/= Q ) /\ ( R e. A /\ -. R .<_ W ) ) ) -> F =/= .0. )

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
    c.0
    cF
    @13
    cR
    c.0
    c.or
    co
    #
    cR
    cF
    c.or
    co
    #
    wne
    #
    c.0
    cF
    wne
    @13
    @0
    @14
    cK
    cbs
    cfv
    #
    wcel
    #
    @15
    @17
    wcel
    #
    @14
    @15
    cK
    ccvr
    cfv
    #
    wbr
    @16
    @0
    @1
    @12
    simpll
    #
    @13
    cK
    clat
    wcel
    #
    cR
    @17
    wcel
    #
    c.0
    @17
    wcel
    #
    @18
    @0
    @22
    @1
    @12
    cK
    hllat
    ad2antrr
    #
    @13
    @9
    @23
    @9
    @10
    @5
    @8
    @2
    simpr3l
    #
    cA
    @17
    cR
    cK
    @17
    eqid
    #
    cdleme1.a
    atbase
    syl
    #
    @13
    cK
    cops
    wcel
    #
    @24
    @0
    @29
    @1
    @12
    cK
    hlop
    ad2antrr
    @17
    cK
    c.0
    @27
    cdleme3c.z
    op0cl
    syl
    @17
    c.or
    cK
    cR
    c.0
    @27
    cdleme1.j
    latjcl
    syl3anc
    @13
    @22
    @23
    cF
    @17
    wcel
    #
    @19
    @25
    @28
    @13
    @2
    @3
    @6
    @9
    @30
    @2
    @12
    simpl
    #
    @3
    @4
    @8
    @11
    @2
    simpr1l
    #
    @6
    @7
    @5
    @11
    @2
    simpr2l
    #
    @26
    cA
    @17
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
    @27
    cdleme1b
    syl13anc
    @17
    c.or
    cK
    cR
    cF
    @27
    cdleme1.j
    latjcl
    syl3anc
    @13
    cR
    cR
    cU
    c.or
    co
    #
    @14
    @15
    @20
    @13
    cR
    cU
    wne
    #
    cR
    @34
    @20
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
    @22
    @37
    @17
    wcel
    #
    cW
    @17
    wcel
    #
    @38
    cW
    c.le
    wbr
    @25
    @13
    @22
    cP
    @17
    wcel
    #
    cQ
    @17
    wcel
    #
    @39
    @25
    @13
    @3
    @41
    @32
    cA
    @17
    cP
    cK
    @27
    cdleme1.a
    atbase
    syl
    @13
    @6
    @42
    @33
    cA
    @17
    cQ
    cK
    @27
    cdleme1.a
    atbase
    syl
    @17
    c.or
    cK
    cP
    cQ
    @27
    cdleme1.j
    latjcl
    syl3anc
    @1
    @40
    @0
    @12
    @17
    cH
    cK
    cW
    @27
    cdleme1.h
    lhpbase
    ad2antlr
    @17
    cK
    c.le
    c.an
    @37
    cW
    @27
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
    cU
    cA
    wcel
    #
    @35
    @36
    wb
    @21
    @26
    @2
    @5
    @8
    @43
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
    cA
    @20
    cR
    cU
    c.or
    cK
    cdleme1.j
    @20
    eqid
    #
    cdleme1.a
    atcvr1
    syl3anc
    mpbid
    @13
    cK
    col
    wcel
    #
    @23
    @14
    cR
    wceq
    @0
    @45
    @1
    @12
    cK
    hlol
    ad2antrr
    @28
    @17
    c.or
    cK
    cR
    c.0
    @27
    cdleme1.j
    cdleme3c.z
    olj01
    syl2anc
    @13
    @2
    @3
    @6
    @11
    @15
    @34
    wceq
    @31
    @32
    @33
    @2
    @5
    @8
    @11
    simpr3
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
    syl13anc
    3brtr4d
    chlt
    @17
    @20
    cK
    @14
    @15
    @27
    @44
    cvrne
    syl31anc
    c.0
    cF
    @14
    @15
    c.0
    cF
    cR
    c.or
    oveq2
    necon3i
    syl
    necomd
end
