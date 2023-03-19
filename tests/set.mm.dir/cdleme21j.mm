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
include "simpl33.mm"
include "wi.mm"
include "simpl1.mm"
include "simp22.mm"
include "simp23.mm"
include "simp31l.mm"
include "simp321.mm"
include "simp322.mm"
include "3jca.mm"
include "adantr.mm"
include "simpl21.mm"
include "simp323.mm"
include "anim1i.mm"
include "cdleme21i.mm"
include "syl112anc.mm"
include "mpd.mm"
include "simpl2.mm"
include "simpl31.mm"
include "simpl32.mm"
include "simpr.mm"
include "eqid.mm"
include "cdleme20.mm"
include "syl113anc.mm"
include "pm2.61dan.mm"

theorem cdleme21j
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> N = O )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
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
    w3a
    #
    cP
    cQ
    wne
    #
    cS
    cT
    wne
    #
    wa
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
    @8
    c.le
    wbr
    wn
    #
    cR
    @8
    c.le
    wbr
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
    @13
    c.or
    co
    cQ
    @13
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    #
    w3a
    #
    w3a
    #
    cU
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    #
    cN
    cO
    wceq
    #
    @16
    @18
    wa
    #
    @14
    @19
    @7
    @12
    @14
    @0
    @4
    @18
    simpl33
    @20
    @0
    @2
    @3
    @5
    @9
    @10
    w3a
    #
    w3a
    #
    @1
    @11
    @18
    wa
    @14
    @19
    wi
    @0
    @4
    @15
    @18
    simpl1
    @16
    @22
    @18
    @16
    @2
    @3
    @21
    @0
    @1
    @2
    @3
    @15
    simp22
    @0
    @1
    @2
    @3
    @15
    simp23
    @16
    @5
    @9
    @10
    @5
    @6
    @12
    @14
    @0
    @4
    simp31l
    @9
    @10
    @11
    @7
    @14
    @0
    @4
    simp321
    @9
    @10
    @11
    @7
    @14
    @0
    @4
    simp322
    3jca
    3jca
    adantr
    @1
    @2
    @3
    @0
    @15
    @18
    simpl21
    @16
    @11
    @18
    @9
    @10
    @11
    @7
    @14
    @0
    @4
    simp323
    anim1i
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
    vr
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
    cdleme21i
    syl112anc
    mpd
    @16
    @18
    wn
    #
    wa
    @0
    @4
    @7
    @12
    @23
    @19
    @0
    @4
    @15
    @23
    simpl1
    @0
    @4
    @15
    @23
    simpl2
    @7
    @12
    @14
    @0
    @4
    @23
    simpl31
    @7
    @12
    @14
    @0
    @4
    @23
    simpl32
    @16
    @23
    simpr
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
    @17
    cW
    c.an
    co
    #
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
    @24
    eqid
    cdleme21g.n
    cdleme21g.o
    cdleme20
    syl113anc
    pm2.61dan
end
