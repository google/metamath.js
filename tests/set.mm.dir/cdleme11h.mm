include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp23.mm"
include "simp22l.mm"
include "simp22r.mm"
include "cdleme0c.mm"
include "syl122anc.mm"
include "necomd.mm"
include "wb.mm"
include "simp1l.mm"
include "simp21.mm"
include "simp3r.mm"
include "cdleme00a.mm"
include "syl131anc.mm"
include "cdleme9a.mm"
include "syl112anc.mm"
include "lnnat.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "wceq.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "simp22.mm"
include "simp3l.mm"
include "cdleme11g.mm"
include "sylibd.mm"
include "necon3bd.mm"
include "mpd.mm"

theorem cdleme11h
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ S e. A ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) -> F =/= Q )

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
    cQ
    cC
    c.or
    co
    #
    cA
    wcel
    #
    wn
    #
    cF
    cQ
    wne
    @14
    cQ
    cC
    wne
    #
    @17
    @14
    cC
    cQ
    @14
    @2
    @3
    @9
    @6
    @7
    cC
    cQ
    wne
    @2
    @10
    @13
    simp1
    #
    @3
    @4
    @8
    @9
    @2
    @13
    simp21l
    #
    @2
    @5
    @8
    @9
    @13
    simp23
    #
    @6
    @7
    @5
    @9
    @2
    @13
    simp22l
    #
    @6
    @7
    @5
    @9
    @2
    @13
    simp22r
    cA
    cP
    cS
    cQ
    cC
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
    cdleme0c
    syl122anc
    necomd
    @14
    @0
    @6
    cC
    cA
    wcel
    #
    @18
    @17
    wb
    @0
    @1
    @10
    @13
    simp1l
    #
    @22
    @14
    @2
    @5
    @9
    cP
    cS
    wne
    @23
    @19
    @2
    @5
    @8
    @9
    @13
    simp21
    @21
    @14
    cS
    cP
    @14
    @0
    @3
    @6
    @9
    @12
    cS
    cP
    wne
    @24
    @20
    @22
    @21
    @2
    @10
    @11
    @12
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
    cA
    cQ
    cC
    c.or
    cK
    cdleme11.j
    cdleme11.a
    lnnat
    syl3anc
    mpbid
    @14
    @16
    cF
    cQ
    @14
    cF
    cQ
    wceq
    #
    cQ
    cF
    c.or
    co
    #
    cA
    wcel
    #
    @16
    @14
    @27
    @25
    cQ
    cQ
    c.or
    co
    #
    cA
    wcel
    @14
    @28
    cQ
    cA
    @14
    @0
    @6
    @28
    cQ
    wceq
    @24
    @22
    cA
    c.or
    cK
    cQ
    cdleme11.j
    cdleme11.a
    hlatjidm
    syl2anc
    @22
    eqeltrd
    @25
    @26
    @28
    cA
    cF
    cQ
    cQ
    c.or
    oveq2
    eleq1d
    syl5ibrcom
    @14
    @26
    @15
    cA
    @14
    @2
    @3
    @8
    @9
    @11
    @26
    @15
    wceq
    @19
    @20
    @2
    @5
    @8
    @9
    @13
    simp22
    @21
    @2
    @10
    @11
    @12
    simp3l
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
    cdleme11g
    syl131anc
    eleq1d
    sylibd
    necon3bd
    mpd
end
