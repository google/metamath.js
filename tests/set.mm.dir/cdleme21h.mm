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
include "simp11.mm"
include "simp12.mm"
include "simp13l.mm"
include "simp13r.mm"
include "simp2.mm"
include "simp3l.mm"
include "simp3r.mm"
include "jca31.mm"
include "cdleme21g.mm"
include "syl113anc.mm"
include "rexlimdv3a.mm"

theorem cdleme21h
  let vz: setvar z
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
  disjoint r z
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( R .<_ ( P .\/ Q ) /\ U .<_ ( S .\/ T ) ) ) ) -> ( E. z e. A ( -. z .<_ W /\ ( P .\/ z ) = ( S .\/ z ) ) -> N = O ) )

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
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    cT
    cA
    wcel
    cT
    cW
    c.le
    wbr
    wn
    wa
    cP
    cQ
    wne
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    cT
    @1
    c.le
    wbr
    wn
    w3a
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
    cR
    @1
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
    #
    wa
    #
    w3a
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    cP
    @7
    c.or
    co
    cS
    @7
    c.or
    co
    wceq
    #
    wa
    #
    cN
    cO
    wceq
    #
    vz
    cA
    @6
    @7
    cA
    wcel
    #
    @10
    w3a
    #
    @0
    @2
    @3
    @4
    @12
    @8
    wa
    @9
    wa
    @11
    @0
    @2
    @5
    @12
    @10
    simp11
    @0
    @2
    @5
    @12
    @10
    simp12
    @3
    @4
    @0
    @2
    @12
    @10
    simp13l
    @3
    @4
    @0
    @2
    @12
    @10
    simp13r
    @13
    @12
    @8
    @9
    @6
    @12
    @10
    simp2
    @6
    @12
    @8
    @9
    simp3l
    @6
    @12
    @8
    @9
    simp3r
    jca31
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
    cdleme21g
    syl113anc
    rexlimdv3a
end
