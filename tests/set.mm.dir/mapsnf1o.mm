include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "cixp.mm"
include "ixpsnf1o.mm"
include "adantl.mm"
include "wceq.mm"
include "wb.mm"
include "cvv.mm"
include "snex.mm"
include "ixpconstg.mm"
include "eqcomd.mm"
include "mpan.mm"
include "adantr.mm"
include "f1oeq3.mm"
include "syl.mm"
include "mpbird.mm"

theorem mapsnf1o
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cI: class I
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  assume ixpsnf1o.f: |- F = ( x e. A |-> ( { I } X. { x } ) )

  disjoint I x
  disjoint A x
  disjoint V x
  disjoint W x
  disjoint I a
  disjoint I b
  disjoint I c
  disjoint I y
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint A y
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint V y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F y
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W y
  assert |- ( ( A e. V /\ I e. W ) -> F : A -1-1-onto-> ( A ^m { I } ) )

  proof
    cA
    cV
    wcel
    #
    cI
    cW
    wcel
    #
    wa
    #
    cA
    cA
    cI
    csn
    #
    cmap
    co
    #
    cF
    wf1o
    #
    cA
    vy
    @3
    cA
    cixp
    #
    cF
    wf1o
    #
    @1
    @7
    @0
    vx
    vy
    cA
    cF
    cI
    cW
    ixpsnf1o.f
    ixpsnf1o
    adantl
    @2
    @4
    @6
    wceq
    #
    @5
    @7
    wb
    @0
    @8
    @1
    @3
    cvv
    wcel
    #
    @0
    @8
    cI
    snex
    @9
    @0
    wa
    @6
    @4
    vy
    @3
    cA
    cvv
    cV
    ixpconstg
    eqcomd
    mpan
    adantr
    @4
    @6
    cA
    cF
    f1oeq3
    syl
    mpbird
end
