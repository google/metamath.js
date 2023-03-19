include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "cdlemc6.mm"
include "syl3anc.mm"
include "wne.mm"
include "simpl3.mm"
include "cdlemc5.mm"
include "syl112anc.mm"
include "pm2.61dane.mm"

theorem cdlemc
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemc3.l: |- .<_ = ( le ` K )
  assume cdlemc3.j: |- .\/ = ( join ` K )
  assume cdlemc3.m: |- ./\ = ( meet ` K )
  assume cdlemc3.a: |- A = ( Atoms ` K )
  assume cdlemc3.h: |- H = ( LHyp ` K )
  assume cdlemc3.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemc3.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ -. Q .<_ ( P .\/ ( F ` P ) ) ) -> ( F ` Q ) = ( ( Q .\/ ( R ` F ) ) ./\ ( ( F ` P ) .\/ ( ( P .\/ Q ) ./\ W ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
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
    cQ
    cP
    cP
    cF
    cfv
    #
    c.or
    co
    c.le
    wbr
    wn
    #
    w3a
    #
    cQ
    cF
    cfv
    cQ
    cF
    cR
    cfv
    c.or
    co
    @2
    cP
    cQ
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    wceq
    #
    @2
    cP
    @4
    @2
    cP
    wceq
    #
    wa
    @0
    @1
    @6
    @5
    @0
    @1
    @3
    @6
    simpl1
    @0
    @1
    @3
    @6
    simpl2
    @4
    @6
    simpr
    cA
    cP
    cQ
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemc3.l
    cdlemc3.j
    cdlemc3.m
    cdlemc3.a
    cdlemc3.h
    cdlemc3.t
    cdlemc3.r
    cdlemc6
    syl3anc
    @4
    @2
    cP
    wne
    #
    wa
    @0
    @1
    @3
    @7
    @5
    @0
    @1
    @3
    @7
    simpl1
    @0
    @1
    @3
    @7
    simpl2
    @0
    @1
    @3
    @7
    simpl3
    @4
    @7
    simpr
    cA
    cP
    cQ
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemc3.l
    cdlemc3.j
    cdlemc3.m
    cdlemc3.a
    cdlemc3.h
    cdlemc3.t
    cdlemc3.r
    cdlemc5
    syl112anc
    pm2.61dane
end
