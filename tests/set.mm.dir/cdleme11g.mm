include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "oveq2i.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1l.mm"
include "simp22l.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "simp23.mm"
include "eqid.mm"
include "atbase.mm"
include "simp1.mm"
include "simp21.mm"
include "cdleme0aa.mm"
include "syl3anc.mm"
include "latjcl.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "latlej1.mm"
include "atmod1i1.mm"
include "syl131anc.mm"
include "syl5eq.mm"
include "simp22.mm"
include "cdleme0cq.mm"
include "syl12anc.mm"
include "oveq2d.mm"
include "latj12.mm"
include "syl13anc.mm"
include "latj13.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "latmle1.mm"
include "wi.mm"
include "latjlej2.mm"
include "mpd.mm"
include "wb.mm"
include "latleeqm2.mm"
include "mpbid.mm"
include "syl6eqr.mm"
include "3eqtrd.mm"

theorem cdleme11g
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme11.l: |- .<_ = ( le ` K )
  assume cdleme11.j: |- .\/ = ( join ` K )
  assume cdleme11.m: |- ./\ = ( meet ` K )
  assume cdleme11.a: |- A = ( Atoms ` K )
  assume cdleme11.h: |- H = ( LHyp ` K )
  assume cdleme11.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme11.c: |- C = ( ( P .\/ S ) ./\ W )
  assume cdleme11.d: |- D = ( ( P .\/ T ) ./\ W )
  assume cdleme11.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ ( Q e. A /\ -. Q .<_ W ) /\ S e. A ) /\ P =/= Q ) -> ( Q .\/ F ) = ( Q .\/ C ) )

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
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cS
    cA
    wcel
    #
    w3a
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cQ
    cF
    c.or
    co
    #
    cQ
    cS
    cU
    c.or
    co
    #
    c.or
    co
    #
    cQ
    cP
    cS
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
    cQ
    @14
    c.or
    co
    #
    @16
    c.an
    co
    #
    cQ
    cC
    c.or
    co
    #
    @10
    @11
    cQ
    @12
    @16
    c.an
    co
    #
    c.or
    co
    #
    @17
    cF
    @21
    cQ
    c.or
    cdleme11.f
    oveq2i
    @10
    @0
    @4
    @12
    cK
    cbs
    cfv
    #
    wcel
    #
    @16
    @23
    wcel
    #
    cQ
    @16
    c.le
    wbr
    #
    @22
    @17
    wceq
    @0
    @1
    @8
    @9
    simp1l
    #
    @4
    @5
    @3
    @7
    @2
    @9
    simp22l
    #
    @10
    cK
    clat
    wcel
    #
    cS
    @23
    wcel
    #
    cU
    @23
    wcel
    #
    @24
    @10
    @0
    @29
    @27
    cK
    hllat
    syl
    #
    @10
    @7
    @30
    @2
    @3
    @6
    @7
    @9
    simp23
    cA
    @23
    cS
    cK
    @23
    eqid
    #
    cdleme11.a
    atbase
    syl
    #
    @10
    @2
    @3
    @4
    @31
    @2
    @8
    @9
    simp1
    #
    @2
    @3
    @6
    @7
    @9
    simp21
    #
    @28
    cA
    @23
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme11.h
    cdleme11.u
    @33
    cdleme0aa
    syl3anc
    #
    @23
    c.or
    cK
    cS
    cU
    @33
    cdleme11.j
    latjcl
    syl3anc
    @10
    @29
    cQ
    @23
    wcel
    #
    @15
    @23
    wcel
    #
    @25
    @32
    @10
    @4
    @38
    @28
    cA
    @23
    cQ
    cK
    @33
    cdleme11.a
    atbase
    syl
    #
    @10
    @29
    @14
    @23
    wcel
    #
    cW
    @23
    wcel
    #
    @39
    @32
    @10
    @29
    cP
    @23
    wcel
    #
    @30
    @41
    @32
    @10
    @3
    @43
    @36
    cA
    @23
    cP
    cK
    @33
    cdleme11.a
    atbase
    syl
    #
    @34
    @23
    c.or
    cK
    cP
    cS
    @33
    cdleme11.j
    latjcl
    syl3anc
    #
    @10
    @1
    @42
    @0
    @1
    @8
    @9
    simp1r
    @23
    cH
    cK
    cW
    @33
    cdleme11.h
    lhpbase
    syl
    #
    @23
    cK
    c.an
    @14
    cW
    @33
    cdleme11.m
    latmcl
    syl3anc
    #
    @23
    c.or
    cK
    cQ
    @15
    @33
    cdleme11.j
    latjcl
    syl3anc
    #
    @10
    @29
    @38
    @39
    @26
    @32
    @40
    @47
    @23
    c.or
    cK
    c.le
    cQ
    @15
    @33
    cdleme11.l
    cdleme11.j
    latlej1
    syl3anc
    cA
    @23
    cQ
    c.or
    cK
    c.le
    c.an
    @12
    @16
    @33
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    atmod1i1
    syl131anc
    syl5eq
    @10
    @13
    @18
    @16
    c.an
    @10
    cS
    cQ
    cU
    c.or
    co
    #
    c.or
    co
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.or
    co
    #
    @13
    @18
    @10
    @49
    @51
    cS
    c.or
    @10
    @2
    @3
    @6
    @49
    @51
    wceq
    @35
    @36
    @2
    @3
    @6
    @7
    @9
    simp22
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
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme11.h
    cdleme11.u
    cdleme0cq
    syl12anc
    oveq2d
    @10
    @29
    @38
    @30
    @31
    @13
    @50
    wceq
    @32
    @40
    @34
    @37
    @23
    c.or
    cK
    cQ
    cS
    cU
    @33
    cdleme11.j
    latj12
    syl13anc
    @10
    @29
    @38
    @43
    @30
    @18
    @52
    wceq
    @32
    @40
    @44
    @34
    @23
    c.or
    cK
    cQ
    cP
    cS
    @33
    cdleme11.j
    latj13
    syl13anc
    3eqtr4d
    oveq1d
    @10
    @19
    @16
    @20
    @10
    @16
    @18
    c.le
    wbr
    #
    @19
    @16
    wceq
    #
    @10
    @15
    @14
    c.le
    wbr
    #
    @53
    @10
    @29
    @41
    @42
    @55
    @32
    @45
    @46
    @23
    cK
    c.le
    c.an
    @14
    cW
    @33
    cdleme11.l
    cdleme11.m
    latmle1
    syl3anc
    @10
    @29
    @39
    @41
    @38
    @55
    @53
    wi
    @32
    @47
    @45
    @40
    @23
    c.or
    cK
    c.le
    @15
    @14
    cQ
    @33
    cdleme11.l
    cdleme11.j
    latjlej2
    syl13anc
    mpd
    @10
    @29
    @25
    @18
    @23
    wcel
    #
    @53
    @54
    wb
    @32
    @48
    @10
    @29
    @38
    @41
    @56
    @32
    @40
    @45
    @23
    c.or
    cK
    cQ
    @14
    @33
    cdleme11.j
    latjcl
    syl3anc
    @23
    cK
    c.le
    c.an
    @16
    @18
    @33
    cdleme11.l
    cdleme11.m
    latleeqm2
    syl3anc
    mpbid
    cC
    @15
    cQ
    c.or
    cdleme11.c
    oveq2i
    syl6eqr
    3eqtrd
end
