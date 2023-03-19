include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "w3a.mm"
include "simp33.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "clat.mm"
include "simpl1l.mm"
include "hllat.mm"
include "syl.mm"
include "simpl32.mm"
include "atbase.mm"
include "simpl2l.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simpl31.mm"
include "hlatlej2.mm"
include "wceq.mm"
include "simpl1r.mm"
include "simpl2r.mm"
include "cdleme8.mm"
include "syl221anc.mm"
include "hlatlej1.mm"
include "simpr.mm"
include "wb.mm"
include "cdleme9b.mm"
include "syl13anc.mm"
include "latjle12.mm"
include "mpbi2and.mm"
include "eqbrtrrd.mm"
include "lattrd.mm"
include "mtand.mm"

theorem cdleme17b
  let cA: class A
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme17.l: |- .<_ = ( le ` K )
  assume cdleme17.j: |- .\/ = ( join ` K )
  assume cdleme17.m: |- ./\ = ( meet ` K )
  assume cdleme17.a: |- A = ( Atoms ` K )
  assume cdleme17.h: |- H = ( LHyp ` K )
  assume cdleme17.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme17.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme17.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme17.c: |- C = ( ( P .\/ S ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ S e. A /\ -. S .<_ ( P .\/ Q ) ) ) -> -. C .<_ ( P .\/ Q ) )

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
    cS
    cA
    wcel
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    w3a
    #
    cC
    @8
    c.le
    wbr
    #
    @9
    @2
    @5
    @6
    @7
    @10
    simp33
    @12
    @13
    wa
    #
    cK
    cbs
    cfv
    #
    cK
    c.le
    cS
    cP
    cS
    c.or
    co
    #
    @8
    @15
    eqid
    #
    cdleme17.l
    @14
    @0
    cK
    clat
    wcel
    #
    @0
    @1
    @5
    @11
    @13
    simpl1l
    #
    cK
    hllat
    syl
    #
    @14
    @7
    cS
    @15
    wcel
    @6
    @7
    @10
    @2
    @5
    @13
    simpl32
    #
    cA
    @15
    cS
    cK
    @17
    cdleme17.a
    atbase
    syl
    @14
    @0
    @3
    @7
    @16
    @15
    wcel
    @19
    @3
    @4
    @2
    @11
    @13
    simpl2l
    #
    @21
    cA
    @15
    c.or
    cK
    cP
    cS
    @17
    cdleme17.j
    cdleme17.a
    hlatjcl
    syl3anc
    @14
    @0
    @3
    @6
    @8
    @15
    wcel
    #
    @19
    @22
    @6
    @7
    @10
    @2
    @5
    @13
    simpl31
    #
    cA
    @15
    c.or
    cK
    cP
    cQ
    @17
    cdleme17.j
    cdleme17.a
    hlatjcl
    syl3anc
    #
    @14
    @0
    @3
    @7
    cS
    @16
    c.le
    wbr
    @19
    @22
    @21
    cA
    cP
    cS
    c.or
    cK
    c.le
    cdleme17.l
    cdleme17.j
    cdleme17.a
    hlatlej2
    syl3anc
    @14
    cP
    cC
    c.or
    co
    #
    @16
    @8
    c.le
    @14
    @0
    @1
    @3
    @4
    @7
    @26
    @16
    wceq
    @19
    @0
    @1
    @5
    @11
    @13
    simpl1r
    #
    @22
    @3
    @4
    @2
    @11
    @13
    simpl2r
    @21
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
    cdleme17.l
    cdleme17.j
    cdleme17.m
    cdleme17.a
    cdleme17.h
    cdleme17.c
    cdleme8
    syl221anc
    @14
    cP
    @8
    c.le
    wbr
    #
    @13
    @26
    @8
    c.le
    wbr
    #
    @14
    @0
    @3
    @6
    @28
    @19
    @22
    @24
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdleme17.l
    cdleme17.j
    cdleme17.a
    hlatlej1
    syl3anc
    @12
    @13
    simpr
    @14
    @18
    cP
    @15
    wcel
    #
    cC
    @15
    wcel
    #
    @23
    @28
    @13
    wa
    @29
    wb
    @20
    @14
    @3
    @30
    @22
    cA
    @15
    cP
    cK
    @17
    cdleme17.a
    atbase
    syl
    @14
    @0
    @3
    @7
    @1
    @31
    @19
    @22
    @21
    @27
    cA
    @15
    cC
    cP
    cS
    cH
    c.or
    cK
    c.an
    cW
    @17
    cdleme17.j
    cdleme17.m
    cdleme17.a
    cdleme17.h
    cdleme17.c
    cdleme9b
    syl13anc
    @25
    @15
    c.or
    cK
    c.le
    cP
    cC
    @8
    @17
    cdleme17.l
    cdleme17.j
    latjle12
    syl13anc
    mpbi2and
    eqbrtrrd
    lattrd
    mtand
end
