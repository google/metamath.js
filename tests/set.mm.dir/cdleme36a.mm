include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "simp3r.mm"
include "wi.mm"
include "simp11l.mm"
include "simp22l.mm"
include "simp3ll.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "cdleme0a.mm"
include "syl112anc.mm"
include "simp12l.mm"
include "simp22.mm"
include "cdleme0c.mm"
include "syl121anc.mm"
include "necomd.mm"
include "hlatexch2.mm"
include "syl131anc.mm"
include "wceq.mm"
include "simp3l.mm"
include "cdleme1.mm"
include "syl13anc.mm"
include "breq2d.mm"
include "simp23.mm"
include "cdleme4.mm"
include "3imtr4d.mm"
include "mtod.mm"

theorem cdleme36a
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cE: class E
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdleme36.b: |- B = ( Base ` K )
  assume cdleme36.l: |- .<_ = ( le ` K )
  assume cdleme36.j: |- .\/ = ( join ` K )
  assume cdleme36.m: |- ./\ = ( meet ` K )
  assume cdleme36.a: |- A = ( Atoms ` K )
  assume cdleme36.h: |- H = ( LHyp ` K )
  assume cdleme36.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme36.e: |- E = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ R .<_ ( P .\/ Q ) ) /\ ( ( t e. A /\ -. t .<_ W ) /\ -. t .<_ ( P .\/ Q ) ) ) -> -. R .<_ ( t .\/ E ) )

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
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    vt
    cv
    #
    cA
    wcel
    #
    @15
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @15
    @12
    c.le
    wbr
    #
    wn
    #
    wa
    #
    w3a
    #
    cR
    @15
    cE
    c.or
    co
    #
    c.le
    wbr
    #
    @19
    @7
    @14
    @18
    @20
    simp3r
    @22
    cR
    @15
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    @15
    cR
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    @24
    @19
    @22
    @0
    @9
    @16
    cU
    cA
    wcel
    #
    cR
    cU
    wne
    @26
    @28
    wi
    @0
    @1
    @5
    @6
    @14
    @21
    simp11l
    @9
    @10
    @8
    @13
    @7
    @21
    simp22l
    @16
    @17
    @20
    @7
    @14
    simp3ll
    @22
    @2
    @5
    @6
    @8
    @29
    @2
    @5
    @6
    @14
    @21
    simp11
    #
    @2
    @5
    @6
    @14
    @21
    simp12
    @2
    @5
    @6
    @14
    @21
    simp13
    #
    @7
    @8
    @11
    @13
    @21
    simp21
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
    cdleme36.l
    cdleme36.j
    cdleme36.m
    cdleme36.a
    cdleme36.h
    cdleme36.u
    cdleme0a
    syl112anc
    @22
    cU
    cR
    @22
    @2
    @3
    @6
    @11
    cU
    cR
    wne
    @30
    @3
    @4
    @2
    @6
    @14
    @21
    simp12l
    #
    @31
    @7
    @8
    @11
    @13
    @21
    simp22
    #
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
    cW
    cdleme36.l
    cdleme36.j
    cdleme36.m
    cdleme36.a
    cdleme36.h
    cdleme36.u
    cdleme0c
    syl121anc
    necomd
    cA
    cR
    @15
    cU
    c.or
    cK
    c.le
    cdleme36.l
    cdleme36.j
    cdleme36.a
    hlatexch2
    syl131anc
    @22
    @23
    @25
    cR
    c.le
    @22
    @2
    @3
    @6
    @18
    @23
    @25
    wceq
    @30
    @32
    @31
    @7
    @14
    @18
    @20
    simp3l
    cA
    cP
    cQ
    @15
    cU
    cE
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme36.l
    cdleme36.j
    cdleme36.m
    cdleme36.a
    cdleme36.h
    cdleme36.u
    cdleme36.e
    cdleme1
    syl13anc
    breq2d
    @22
    @12
    @27
    @15
    c.le
    @22
    @2
    @3
    @6
    @11
    @13
    @12
    @27
    wceq
    @30
    @32
    @31
    @33
    @7
    @8
    @11
    @13
    @21
    simp23
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
    cW
    cdleme36.l
    cdleme36.j
    cdleme36.m
    cdleme36.a
    cdleme36.h
    cdleme36.u
    cdleme4
    syl131anc
    breq2d
    3imtr4d
    mtod
end
