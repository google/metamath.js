include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cdleme11j.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp21l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp23l.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "wb.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22l.mm"
include "simp3r.mm"
include "cdleme00a.mm"
include "syl131anc.mm"
include "necomd.mm"
include "cdleme9a.mm"
include "syl112anc.mm"
include "cdleme3fa.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cal.mm"
include "hlatl.mm"
include "simp22.mm"
include "simp3.mm"
include "cdleme11h.mm"
include "lhpat.mm"
include "atcmp.mm"
include "mpbid.mm"

theorem cdleme11k
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) -> C = ( ( Q .\/ F ) ./\ W ) )

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
    w3a
    #
    cP
    cQ
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cC
    cQ
    cF
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.le
    wbr
    #
    cC
    @18
    wceq
    #
    @16
    cC
    @17
    c.le
    wbr
    #
    cC
    cW
    c.le
    wbr
    #
    @19
    cA
    cC
    cU
    cP
    cQ
    cS
    cQ
    cU
    cF
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
    cdleme11.c
    cdleme11.u
    cdleme11.f
    cdleme11j
    @16
    cC
    cP
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdleme11.c
    @16
    cK
    clat
    wcel
    #
    @23
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @26
    wcel
    #
    @24
    cW
    c.le
    wbr
    @16
    @0
    @25
    @0
    @1
    @12
    @15
    simp1l
    #
    cK
    hllat
    syl
    #
    @16
    @25
    cP
    @26
    wcel
    #
    cS
    @26
    wcel
    #
    @27
    @30
    @16
    @3
    @31
    @3
    @4
    @8
    @11
    @2
    @15
    simp21l
    #
    cA
    @26
    cP
    cK
    @26
    eqid
    #
    cdleme11.a
    atbase
    syl
    @16
    @9
    @32
    @9
    @10
    @5
    @8
    @2
    @15
    simp23l
    #
    cA
    @26
    cS
    cK
    @34
    cdleme11.a
    atbase
    syl
    @26
    c.or
    cK
    cP
    cS
    @34
    cdleme11.j
    latjcl
    syl3anc
    @16
    @1
    @28
    @0
    @1
    @12
    @15
    simp1r
    @26
    cH
    cK
    cW
    @34
    cdleme11.h
    lhpbase
    syl
    #
    @26
    cK
    c.le
    c.an
    @23
    cW
    @34
    cdleme11.l
    cdleme11.m
    latmle2
    syl3anc
    syl5eqbr
    @16
    @25
    cC
    @26
    wcel
    #
    @17
    @26
    wcel
    #
    @28
    @21
    @22
    wa
    @19
    wb
    @30
    @16
    cC
    cA
    wcel
    #
    @37
    @16
    @2
    @5
    @9
    cP
    cS
    wne
    @39
    @2
    @12
    @15
    simp1
    #
    @2
    @5
    @8
    @11
    @15
    simp21
    #
    @35
    @16
    cS
    cP
    @16
    @0
    @3
    @6
    @9
    @14
    cS
    cP
    wne
    @29
    @33
    @6
    @7
    @5
    @11
    @2
    @15
    simp22l
    #
    @35
    @2
    @12
    @13
    @14
    simp3r
    cA
    cP
    cQ
    cS
    c.or
    cK
    c.le
    c.an
    cdleme11.l
    cdleme11.j
    cdleme11.m
    cdleme11.a
    cdleme00a
    syl131anc
    necomd
    cA
    cC
    cP
    cS
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
    cdleme11.c
    cdleme9a
    syl112anc
    #
    cA
    @26
    cC
    cK
    @34
    cdleme11.a
    atbase
    syl
    @16
    @25
    cQ
    @26
    wcel
    #
    cF
    @26
    wcel
    #
    @38
    @30
    @16
    @6
    @44
    @42
    cA
    @26
    cQ
    cK
    @34
    cdleme11.a
    atbase
    syl
    @16
    cF
    cA
    wcel
    #
    @45
    cA
    cP
    cQ
    cS
    cU
    cF
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
    cdleme11.f
    cdleme3fa
    #
    cA
    @26
    cF
    cK
    @34
    cdleme11.a
    atbase
    syl
    @26
    c.or
    cK
    cQ
    cF
    @34
    cdleme11.j
    latjcl
    syl3anc
    @36
    @26
    cK
    c.le
    c.an
    cC
    @17
    cW
    @34
    cdleme11.l
    cdleme11.m
    latlem12
    syl13anc
    mpbi2and
    @16
    cK
    cal
    wcel
    #
    @39
    @18
    cA
    wcel
    #
    @19
    @20
    wb
    @16
    @0
    @48
    @29
    cK
    hlatl
    syl
    @43
    @16
    @2
    @8
    @46
    cQ
    cF
    wne
    @49
    @40
    @2
    @5
    @8
    @11
    @15
    simp22
    #
    @47
    @16
    cF
    cQ
    @16
    @2
    @5
    @8
    @9
    @15
    cF
    cQ
    wne
    @40
    @41
    @50
    @35
    @2
    @12
    @15
    simp3
    cA
    cC
    cU
    cP
    cQ
    cS
    cQ
    cU
    cF
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
    cdleme11.c
    cdleme11.u
    cdleme11.f
    cdleme11h
    syl131anc
    necomd
    cA
    cQ
    cF
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
    lhpat
    syl112anc
    cA
    cC
    @18
    cK
    c.le
    cdleme11.l
    cdleme11.a
    atcmp
    syl3anc
    mpbid
end
