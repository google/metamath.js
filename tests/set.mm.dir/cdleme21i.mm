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
include "simpl11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21l.mm"
include "3jca.mm"
include "adantr.mm"
include "simp231.mm"
include "simp232.mm"
include "simpr.mm"
include "4atexlem7.mm"
include "syl113anc.mm"
include "ex.mm"
include "cdleme21h.mm"
include "syld.mm"

theorem cdleme21i
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cY: class Y
  let vr: setvar r
  let vz: setvar z
  assume cdleme21.l: |- .<_ = ( le ` K )
  assume cdleme21.j: |- .\/ = ( join ` K )
  assume cdleme21.m: |- ./\ = ( meet ` K )
  assume cdleme21.a: |- A = ( Atoms ` K )
  assume cdleme21.h: |- H = ( LHyp ` K )
  assume cdleme21.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme21.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme21g.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme21g.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme21g.y: |- Y = ( ( R .\/ T ) ./\ W )
  assume cdleme21g.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ D ) )
  assume cdleme21g.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ Y ) )

  disjoint A r
  disjoint F r
  disjoint G r
  disjoint H r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint ./\ r
  disjoint P r
  disjoint Q r
  disjoint R r
  disjoint S r
  disjoint T r
  disjoint W r
  disjoint r z
  disjoint A z
  disjoint H z
  disjoint .\/ z
  disjoint K z
  disjoint .<_ z
  disjoint N z
  disjoint O z
  disjoint P z
  disjoint Q z
  disjoint R z
  disjoint S z
  disjoint T z
  disjoint U z
  disjoint W z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( R .<_ ( P .\/ Q ) /\ U .<_ ( S .\/ T ) ) ) ) -> ( E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) -> N = O ) )

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
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
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
    cT
    cA
    wcel
    cT
    cW
    c.le
    wbr
    wn
    wa
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
    cT
    @9
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
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
    cR
    @9
    c.le
    wbr
    cU
    cS
    cT
    c.or
    co
    c.le
    wbr
    wa
    wa
    #
    w3a
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
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @18
    c.or
    co
    cS
    @18
    c.or
    co
    wceq
    wa
    vz
    cA
    wrex
    #
    cN
    cO
    wceq
    @15
    @17
    @19
    @15
    @17
    wa
    @0
    @1
    @2
    @4
    w3a
    #
    @8
    @10
    @17
    @19
    @0
    @1
    @2
    @13
    @14
    @17
    simpl11
    @15
    @20
    @17
    @15
    @1
    @2
    @4
    @0
    @1
    @2
    @13
    @14
    simp12
    @0
    @1
    @2
    @13
    @14
    simp13
    @4
    @5
    @7
    @12
    @3
    @14
    simp21l
    3jca
    adantr
    @15
    @8
    @17
    @8
    @10
    @11
    @6
    @7
    @3
    @14
    simp231
    adantr
    @15
    @10
    @17
    @8
    @10
    @11
    @6
    @7
    @3
    @14
    simp232
    adantr
    @15
    @17
    simpr
    vz
    cA
    cP
    cQ
    cS
    cH
    c.or
    cK
    c.le
    cW
    vr
    cdleme21.l
    cdleme21.j
    cdleme21.a
    cdleme21.h
    4atexlem7
    syl113anc
    ex
    vz
    cA
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cY
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21.f
    cdleme21g.g
    cdleme21g.d
    cdleme21g.y
    cdleme21g.n
    cdleme21g.o
    cdleme21h
    syld
end
