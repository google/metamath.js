include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wa.mm"
include "wrex.mm"
include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "4atexlemswapqr.mm"
include "wi.mm"
include "4atexlemcnd.mm"
include "pm13.18.mm"
include "necomd.mm"
include "expcom.mm"
include "syl.mm"
include "biid.mm"
include "eqid.mm"
include "4atexlemex2.mm"
include "syl6an.mm"
include "imp.mm"

theorem 4atexlemex4
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume 4thatlem.ph: |- ( ph <-> ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( S e. A /\ ( R e. A /\ -. R .<_ W /\ ( P .\/ R ) = ( Q .\/ R ) ) /\ ( T e. A /\ ( U .\/ T ) = ( V .\/ T ) ) ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) ) ) )
  assume 4thatlem0.l: |- .<_ = ( le ` K )
  assume 4thatlem0.j: |- .\/ = ( join ` K )
  assume 4thatlem0.m: |- ./\ = ( meet ` K )
  assume 4thatlem0.a: |- A = ( Atoms ` K )
  assume 4thatlem0.h: |- H = ( LHyp ` K )
  assume 4thatlem0.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume 4thatlem0.v: |- V = ( ( P .\/ S ) ./\ W )
  assume 4thatlem0.c: |- C = ( ( Q .\/ T ) ./\ ( P .\/ S ) )
  assume 4thatlem0.d: |- D = ( ( R .\/ T ) ./\ ( P .\/ S ) )

  disjoint A z
  disjoint C z
  disjoint .\/ z
  disjoint .<_ z
  disjoint P z
  disjoint S z
  disjoint W z
  disjoint D z
  assert |- ( ( ph /\ C = S ) -> E. z e. A ( -. z .<_ W /\ ( P .\/ z ) = ( S .\/ z ) ) )

  proof
    wph
    cC
    cS
    wceq
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @1
    c.or
    co
    cS
    @1
    c.or
    co
    wceq
    wa
    vz
    cA
    wrex
    #
    wph
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
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    w3a
    cS
    cA
    wcel
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    cP
    cQ
    c.or
    co
    cR
    cQ
    c.or
    co
    wceq
    w3a
    cT
    cA
    wcel
    cP
    cR
    c.or
    co
    #
    cW
    c.an
    co
    #
    cT
    c.or
    co
    cV
    cT
    c.or
    co
    wceq
    wa
    w3a
    cP
    cR
    wne
    cS
    @3
    c.le
    wbr
    wn
    wa
    w3a
    #
    @0
    cD
    cS
    wne
    #
    @2
    wph
    cA
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    4thatlem.ph
    4thatlem0.l
    4thatlem0.j
    4thatlem0.a
    4thatlem0.u
    4atexlemswapqr
    wph
    cC
    cD
    wne
    #
    @0
    @6
    wi
    wph
    cA
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    4thatlem.ph
    4thatlem0.l
    4thatlem0.j
    4thatlem0.m
    4thatlem0.a
    4thatlem0.h
    4thatlem0.u
    4thatlem0.v
    4thatlem0.c
    4thatlem0.d
    4atexlemcnd
    @0
    @7
    @6
    @0
    @7
    wa
    cS
    cD
    cC
    cS
    cD
    pm13.18
    necomd
    expcom
    syl
    @5
    vz
    cA
    cD
    cP
    cR
    cQ
    cS
    cT
    @4
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    @5
    biid
    4thatlem0.l
    4thatlem0.j
    4thatlem0.m
    4thatlem0.a
    4thatlem0.h
    @4
    eqid
    4thatlem0.v
    4thatlem0.d
    4atexlemex2
    syl6an
    imp
end
