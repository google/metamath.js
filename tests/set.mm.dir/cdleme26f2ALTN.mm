include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wn.mm"
include "w3a.mm"
include "simp11.mm"
include "simp23.mm"
include "simp31r.mm"
include "simp12r.mm"
include "simp12l.mm"
include "3jca.mm"
include "simp21.mm"
include "simp22.mm"
include "simp13.mm"
include "simp32.mm"
include "simp33.mm"
include "cdleme22f2.mm"
include "syl323anc.mm"
include "wceq.mm"
include "simp23l.mm"
include "simp23r.mm"
include "cdleme25cl.mm"
include "syl322anc.mm"
include "simp13l.mm"
include "simp31.mm"
include "cbs.mm"
include "cfv.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "riotasv.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "breqtrrd.mm"

theorem cdleme26f2ALTN
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cT: class T
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  let cV: class V
  let cW: class W
  let vs: setvar s
  assume cdleme26.b: |- B = ( Base ` K )
  assume cdleme26.l: |- .<_ = ( le ` K )
  assume cdleme26.j: |- .\/ = ( join ` K )
  assume cdleme26.m: |- ./\ = ( meet ` K )
  assume cdleme26.a: |- A = ( Atoms ` K )
  assume cdleme26.h: |- H = ( LHyp ` K )
  assume cdleme26f2.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme26f2.f: |- G = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme26f2.n: |- O = ( ( P .\/ Q ) ./\ ( G .\/ ( ( T .\/ s ) ./\ W ) ) )
  assume cdleme26f2.e: |- E = ( iota_ u e. B A. s e. A ( ( -. s .<_ W /\ -. s .<_ ( P .\/ Q ) ) -> u = O ) )

  disjoint s u
  disjoint A s
  disjoint A u
  disjoint B s
  disjoint B u
  disjoint H s
  disjoint .\/ s
  disjoint .\/ u
  disjoint K s
  disjoint .<_ s
  disjoint .<_ u
  disjoint ./\ s
  disjoint ./\ u
  disjoint O u
  disjoint P s
  disjoint P u
  disjoint Q s
  disjoint Q u
  disjoint T s
  disjoint T u
  disjoint U s
  disjoint U u
  disjoint W s
  disjoint W u
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P =/= Q /\ T .<_ ( P .\/ Q ) ) /\ ( s e. A /\ -. s .<_ W ) ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( ( -. s .<_ W /\ -. s .<_ ( P .\/ Q ) ) /\ ( s =/= T /\ s .<_ ( T .\/ V ) ) /\ ( V e. A /\ V .<_ W ) ) ) -> G .<_ ( E .\/ V ) )

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
    cQ
    wne
    #
    cT
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    vs
    cv
    #
    cA
    wcel
    #
    @5
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
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cT
    cA
    wcel
    #
    cT
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    @7
    @5
    @2
    c.le
    wbr
    wn
    #
    wa
    #
    @5
    cT
    wne
    @5
    cT
    cV
    c.or
    co
    c.le
    wbr
    wa
    #
    cV
    cA
    wcel
    cV
    cW
    c.le
    wbr
    wa
    #
    w3a
    #
    w3a
    #
    cG
    cO
    cV
    c.or
    co
    #
    cE
    cV
    c.or
    co
    c.le
    @21
    @0
    @14
    @16
    @3
    @1
    w3a
    @10
    @11
    @8
    @18
    @19
    cG
    @22
    c.le
    wbr
    @0
    @4
    @8
    @15
    @20
    simp11
    #
    @9
    @10
    @11
    @14
    @20
    simp23
    @21
    @16
    @3
    @1
    @7
    @16
    @18
    @19
    @9
    @15
    simp31r
    @1
    @3
    @0
    @8
    @15
    @20
    simp12r
    #
    @1
    @3
    @0
    @8
    @15
    @20
    simp12l
    #
    3jca
    @9
    @10
    @11
    @14
    @20
    simp21
    #
    @9
    @10
    @11
    @14
    @20
    simp22
    #
    @0
    @4
    @8
    @15
    @20
    simp13
    @9
    @15
    @17
    @18
    @19
    simp32
    @9
    @15
    @17
    @18
    @19
    simp33
    cA
    cP
    cQ
    @5
    cT
    cU
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cO
    cV
    cW
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme26f2.u
    cdleme26f2.f
    cdleme26f2.n
    cdleme22f2
    syl323anc
    @21
    cE
    cO
    cV
    c.or
    @21
    cE
    cB
    wcel
    #
    @6
    @17
    cE
    cO
    wceq
    @21
    @0
    @10
    @11
    @12
    @13
    @1
    @3
    @28
    @23
    @26
    @27
    @12
    @13
    @10
    @11
    @9
    @20
    simp23l
    @12
    @13
    @10
    @11
    @9
    @20
    simp23r
    @25
    @24
    vu
    cA
    cB
    cP
    cQ
    cT
    cU
    cG
    cH
    cE
    c.or
    cK
    c.le
    c.an
    cO
    cW
    vs
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme26f2.u
    cdleme26f2.f
    cdleme26f2.n
    cdleme26f2.e
    cdleme25cl
    syl322anc
    @6
    @7
    @0
    @4
    @15
    @20
    simp13l
    @9
    @15
    @17
    @18
    @19
    simp31
    @17
    vu
    vs
    cB
    cA
    cO
    cE
    cB
    cK
    cbs
    cfv
    cvv
    cdleme26.b
    cK
    cbs
    fvex
    eqeltri
    cdleme26f2.e
    riotasv
    syl3anc
    oveq1d
    breqtrrd
end
