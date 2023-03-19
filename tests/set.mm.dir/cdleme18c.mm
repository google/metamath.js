include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "simp31.mm"
include "simp32.mm"
include "jca.mm"
include "cdleme18b.mm"
include "syld3an3.mm"
include "neneqd.mm"
include "wo.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp23l.mm"
include "cdleme4a.mm"
include "syl231anc.mm"
include "simp33.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "cdleme7ga.mm"
include "syl323anc.mm"
include "cdleme18a.mm"
include "cdleme0nex.mm"
include "syl332anc.mm"
include "ord.mm"
include "mt3d.mm"

theorem cdleme18c
  let cA: class A
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
  let vr: setvar r
  assume cdleme18.l: |- .<_ = ( le ` K )
  assume cdleme18.j: |- .\/ = ( join ` K )
  assume cdleme18.m: |- ./\ = ( meet ` K )
  assume cdleme18.a: |- A = ( Atoms ` K )
  assume cdleme18.h: |- H = ( LHyp ` K )
  assume cdleme18.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme18.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme18.g: |- G = ( ( P .\/ Q ) ./\ ( F .\/ ( ( Q .\/ S ) ./\ W ) ) )

  disjoint A r
  disjoint G r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> G = P )

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
    #
    c.le
    wbr
    wn
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @16
    c.or
    co
    cQ
    @16
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    wn
    #
    w3a
    #
    w3a
    #
    cG
    cP
    wceq
    #
    cG
    cQ
    wceq
    #
    @19
    cG
    cQ
    @2
    @12
    @18
    @13
    @15
    wa
    #
    cG
    cQ
    wne
    @19
    @13
    @15
    @2
    @12
    @13
    @15
    @17
    simp31
    #
    @2
    @12
    @13
    @15
    @17
    simp32
    #
    jca
    #
    cA
    cP
    cQ
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme18.l
    cdleme18.j
    cdleme18.m
    cdleme18.a
    cdleme18.h
    cdleme18.u
    cdleme18.f
    cdleme18.g
    cdleme18b
    syld3an3
    neneqd
    @19
    @20
    @21
    @19
    @0
    cG
    @14
    c.le
    wbr
    #
    @17
    @3
    @6
    @13
    cG
    cA
    wcel
    #
    cG
    cW
    c.le
    wbr
    wn
    #
    @20
    @21
    wo
    @0
    @1
    @12
    @18
    simp1l
    #
    @19
    @0
    @1
    @3
    @6
    @6
    @9
    @26
    @29
    @0
    @1
    @12
    @18
    simp1r
    @3
    @4
    @8
    @11
    @2
    @18
    simp21l
    #
    @6
    @7
    @5
    @11
    @2
    @18
    simp22l
    #
    @31
    @9
    @10
    @5
    @8
    @2
    @18
    simp23l
    cA
    cP
    cQ
    cQ
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme18.l
    cdleme18.j
    cdleme18.m
    cdleme18.a
    cdleme18.h
    cdleme18.u
    cdleme18.f
    cdleme18.g
    cdleme4a
    syl231anc
    @2
    @12
    @13
    @15
    @17
    simp33
    @30
    @31
    @23
    @19
    @2
    @5
    @8
    @8
    @11
    @13
    cQ
    @14
    c.le
    wbr
    #
    @15
    @27
    @2
    @12
    @18
    simp1
    @2
    @5
    @8
    @11
    @18
    simp21
    @2
    @5
    @8
    @11
    @18
    simp22
    #
    @33
    @2
    @5
    @8
    @11
    @18
    simp23
    @23
    @19
    @0
    @3
    @6
    @32
    @29
    @30
    @31
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdleme18.l
    cdleme18.j
    cdleme18.a
    hlatlej2
    syl3anc
    @24
    cA
    cP
    cQ
    cQ
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme18.l
    cdleme18.j
    cdleme18.m
    cdleme18.a
    cdleme18.h
    cdleme18.u
    cdleme18.f
    cdleme18.g
    cdleme7ga
    syl323anc
    @2
    @12
    @18
    @22
    @28
    @25
    cA
    cP
    cQ
    cS
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme18.l
    cdleme18.j
    cdleme18.m
    cdleme18.a
    cdleme18.h
    cdleme18.u
    cdleme18.f
    cdleme18.g
    cdleme18a
    syld3an3
    cA
    cP
    cQ
    cG
    c.or
    cK
    c.le
    cW
    vr
    cdleme18.l
    cdleme18.j
    cdleme18.a
    cdleme0nex
    syl332anc
    ord
    mt3d
end
