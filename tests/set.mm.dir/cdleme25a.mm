include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wrex.mm"
include "simp11l.mm"
include "simp11r.mm"
include "simp12.mm"
include "simp13.mm"
include "simp3l.mm"
include "cdlemb2.mm"
include "syl221anc.mm"
include "adantr.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simpl2l.mm"
include "simpr.mm"
include "cdleme22gb.mm"
include "syl222anc.mm"
include "a1d.mm"
include "ancld.mm"
include "reximdva.mm"
include "mpd.mm"

theorem cdleme25a
  let cA: class A
  let cB: class B
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
  let cN: class N
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  assume cdleme24.b: |- B = ( Base ` K )
  assume cdleme24.l: |- .<_ = ( le ` K )
  assume cdleme24.j: |- .\/ = ( join ` K )
  assume cdleme24.m: |- ./\ = ( meet ` K )
  assume cdleme24.a: |- A = ( Atoms ` K )
  assume cdleme24.h: |- H = ( LHyp ` K )
  assume cdleme24.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme24.f: |- F = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme24.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ ( ( R .\/ s ) ./\ W ) ) )

  disjoint A s
  disjoint B s
  disjoint H s
  disjoint .\/ s
  disjoint K s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint W s
  disjoint s t
  disjoint s u
  disjoint t u
  disjoint A t
  disjoint A u
  disjoint B t
  disjoint B u
  disjoint H t
  disjoint .\/ t
  disjoint .\/ u
  disjoint K t
  disjoint .<_ t
  disjoint .<_ u
  disjoint ./\ u
  disjoint P t
  disjoint P u
  disjoint Q t
  disjoint Q u
  disjoint R t
  disjoint R u
  disjoint W t
  disjoint W u
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( R e. A /\ -. R .<_ W ) /\ ( P =/= Q /\ R .<_ ( P .\/ Q ) ) ) -> E. s e. A ( ( -. s .<_ W /\ -. s .<_ ( P .\/ Q ) ) /\ N e. B ) )

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
    w3a
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
    cP
    cQ
    wne
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
    wa
    #
    w3a
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    @18
    @14
    c.le
    wbr
    wn
    wa
    #
    vs
    cA
    wrex
    #
    @19
    cN
    cB
    wcel
    #
    wa
    #
    vs
    cA
    wrex
    @17
    @0
    @1
    @5
    @8
    @13
    @20
    @0
    @1
    @5
    @8
    @12
    @16
    simp11l
    #
    @0
    @1
    @5
    @8
    @12
    @16
    simp11r
    #
    @2
    @5
    @8
    @12
    @16
    simp12
    @2
    @5
    @8
    @12
    @16
    simp13
    @9
    @12
    @13
    @15
    simp3l
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    cW
    vs
    cdleme24.l
    cdleme24.j
    cdleme24.a
    cdleme24.h
    cdlemb2
    syl221anc
    @17
    @19
    @22
    vs
    cA
    @17
    @18
    cA
    wcel
    #
    wa
    #
    @19
    @21
    @26
    @21
    @19
    @26
    @0
    @1
    @3
    @6
    @10
    @25
    @21
    @17
    @0
    @25
    @23
    adantr
    @17
    @1
    @25
    @24
    adantr
    @17
    @3
    @25
    @3
    @4
    @2
    @8
    @12
    @16
    simp12l
    adantr
    @17
    @6
    @25
    @6
    @7
    @2
    @5
    @12
    @16
    simp13l
    adantr
    @10
    @11
    @9
    @16
    @25
    simpl2l
    @17
    @25
    simpr
    cA
    cB
    cP
    cQ
    cR
    @18
    cU
    cF
    cN
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme24.l
    cdleme24.j
    cdleme24.m
    cdleme24.a
    cdleme24.h
    cdleme24.u
    cdleme24.f
    cdleme24.n
    cdleme24.b
    cdleme22gb
    syl222anc
    a1d
    ancld
    reximdva
    mpd
end
