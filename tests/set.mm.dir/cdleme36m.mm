include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "simp11.mm"
include "simp3rl.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21.mm"
include "simp3rr.mm"
include "cdleme3fa.mm"
include "syl132anc.mm"
include "cdleme3.mm"
include "jca.mm"
include "simp13l.mm"
include "cdleme3b.mm"
include "syl13anc.mm"
include "necomd.mm"
include "simp22.mm"
include "simp23.mm"
include "simp3l1.mm"
include "simp3r.mm"
include "cdleme36a.mm"
include "syl331anc.mm"
include "simp3l2.mm"
include "simp3l3.mm"
include "cdleme35h.mm"
include "syl333anc.mm"

theorem cdleme36m
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme36.b: |- B = ( Base ` K )
  assume cdleme36.l: |- .<_ = ( le ` K )
  assume cdleme36.j: |- .\/ = ( join ` K )
  assume cdleme36.m: |- ./\ = ( meet ` K )
  assume cdleme36.a: |- A = ( Atoms ` K )
  assume cdleme36.h: |- H = ( LHyp ` K )
  assume cdleme36.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme36.e: |- E = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme36.v: |- V = ( ( t .\/ E ) ./\ W )
  assume cdleme36.f: |- F = ( ( R .\/ V ) ./\ ( E .\/ ( ( t .\/ R ) ./\ W ) ) )
  assume cdleme36.c: |- C = ( ( S .\/ V ) ./\ ( E .\/ ( ( t .\/ S ) ./\ W ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( ( R .<_ ( P .\/ Q ) /\ S .<_ ( P .\/ Q ) /\ F = C ) /\ ( ( t e. A /\ -. t .<_ W ) /\ -. t .<_ ( P .\/ Q ) ) ) ) -> R = S )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
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
    w3a
    #
    cP
    cQ
    wne
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
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
    cS
    @10
    c.le
    wbr
    #
    cF
    cC
    wceq
    #
    w3a
    #
    vt
    cv
    #
    cA
    wcel
    @15
    cW
    c.le
    wbr
    wn
    wa
    #
    @15
    @10
    c.le
    wbr
    wn
    #
    wa
    #
    wa
    #
    w3a
    #
    @0
    @16
    cE
    cA
    wcel
    #
    cE
    cW
    c.le
    wbr
    wn
    #
    wa
    @15
    cE
    wne
    @7
    @8
    cR
    @15
    cE
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cS
    @23
    c.le
    wbr
    wn
    #
    @13
    cR
    cS
    wceq
    @0
    @1
    @4
    @9
    @19
    simp11
    #
    @16
    @17
    @14
    @5
    @9
    simp3rl
    #
    @20
    @21
    @22
    @20
    @0
    @1
    @4
    @16
    @6
    @17
    @21
    @26
    @0
    @1
    @4
    @9
    @19
    simp12
    #
    @0
    @1
    @4
    @9
    @19
    simp13
    #
    @27
    @5
    @6
    @7
    @8
    @19
    simp21
    #
    @16
    @17
    @14
    @5
    @9
    simp3rr
    #
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
    cdleme3fa
    syl132anc
    @20
    @0
    @1
    @4
    @16
    @6
    @17
    @22
    @26
    @28
    @29
    @27
    @30
    @31
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
    cdleme3
    syl132anc
    jca
    @20
    cE
    @15
    @20
    @0
    @1
    @2
    @6
    wa
    @16
    cE
    @15
    wne
    @26
    @28
    @20
    @2
    @6
    @2
    @3
    @0
    @1
    @9
    @19
    simp13l
    #
    @30
    jca
    @27
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
    cdleme3b
    syl13anc
    necomd
    @5
    @6
    @7
    @8
    @19
    simp22
    #
    @5
    @6
    @7
    @8
    @19
    simp23
    #
    @20
    @0
    @1
    @2
    @6
    @7
    @11
    @18
    @24
    @26
    @28
    @32
    @30
    @33
    @11
    @12
    @13
    @18
    @5
    @9
    simp3l1
    @5
    @9
    @14
    @18
    simp3r
    #
    vt
    cA
    cB
    cP
    cQ
    cR
    cU
    cE
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme36.b
    cdleme36.l
    cdleme36.j
    cdleme36.m
    cdleme36.a
    cdleme36.h
    cdleme36.u
    cdleme36.e
    cdleme36a
    syl331anc
    @20
    @0
    @1
    @2
    @6
    @8
    @12
    @18
    @25
    @26
    @28
    @32
    @30
    @34
    @11
    @12
    @13
    @18
    @5
    @9
    simp3l2
    @35
    vt
    cA
    cB
    cP
    cQ
    cS
    cU
    cE
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme36.b
    cdleme36.l
    cdleme36.j
    cdleme36.m
    cdleme36.a
    cdleme36.h
    cdleme36.u
    cdleme36.e
    cdleme36a
    syl331anc
    @11
    @12
    @13
    @18
    @5
    @9
    simp3l3
    cA
    @15
    cE
    cR
    cS
    cV
    cF
    cC
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
    cdleme36.v
    cdleme36.f
    cdleme36.c
    cdleme35h
    syl333anc
end
