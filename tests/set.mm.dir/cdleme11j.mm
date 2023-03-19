include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp1l.mm"
include "simp22l.mm"
include "cdleme3fa.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp22.mm"
include "simp23l.mm"
include "simp3l.mm"
include "cdleme11g.mm"
include "syl131anc.mm"
include "breqtrd.mm"
include "wi.mm"
include "simp21.mm"
include "simp3r.mm"
include "cdleme00a.mm"
include "necomd.mm"
include "cdleme9a.mm"
include "syl112anc.mm"
include "simp3.mm"
include "cdleme11h.mm"
include "hlatexch1.mm"
include "mpd.mm"

theorem cdleme11j
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


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) -> C .<_ ( Q .\/ F ) )

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
    cF
    cQ
    cC
    c.or
    co
    #
    c.le
    wbr
    #
    cC
    cQ
    cF
    c.or
    co
    #
    c.le
    wbr
    #
    @16
    cF
    @19
    @17
    c.le
    @16
    @0
    @6
    cF
    cA
    wcel
    #
    cF
    @19
    c.le
    wbr
    @0
    @1
    @12
    @15
    simp1l
    #
    @6
    @7
    @5
    @11
    @2
    @15
    simp22l
    #
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
    cQ
    cF
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    hlatlej2
    syl3anc
    @16
    @2
    @3
    @8
    @9
    @13
    @19
    @17
    wceq
    @2
    @12
    @15
    simp1
    #
    @3
    @4
    @8
    @11
    @2
    @15
    simp21l
    #
    @2
    @5
    @8
    @11
    @15
    simp22
    #
    @9
    @10
    @5
    @8
    @2
    @15
    simp23l
    #
    @2
    @12
    @13
    @14
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
    breqtrd
    @16
    @0
    @21
    cC
    cA
    wcel
    #
    @6
    cF
    cQ
    wne
    #
    @18
    @20
    wi
    @22
    @24
    @16
    @2
    @5
    @9
    cP
    cS
    wne
    @29
    @25
    @2
    @5
    @8
    @11
    @15
    simp21
    #
    @28
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
    @22
    @26
    @23
    @28
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
    @23
    @16
    @2
    @5
    @8
    @9
    @15
    @30
    @25
    @31
    @27
    @28
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
    cA
    cF
    cC
    cQ
    c.or
    cK
    c.le
    cdleme11.l
    cdleme11.j
    cdleme11.a
    hlatexch1
    syl131anc
    mpd
end
