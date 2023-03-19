include "ct1.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "simpr3.mm"
include "wceq.mm"
include "t1sep2.mm"
include "3adant3r3.mm"
include "necon3ad.mm"
include "mpd.mm"
include "rexanali.mm"
include "sylibr.mm"

theorem t1sep
  let cA: class A
  let cB: class B
  let vo: setvar o
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cC: class C
  assume t1sep.1: |- X = U. J

  disjoint A o
  disjoint B o
  disjoint J o
  disjoint X o
  disjoint o x
  disjoint o y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  assert |- ( ( J e. Fre /\ ( A e. X /\ B e. X /\ A =/= B ) ) -> E. o e. J ( A e. o /\ -. B e. o ) )

  proof
    cJ
    ct1
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    wa
    #
    cA
    vo
    cv
    #
    wcel
    #
    cB
    @5
    wcel
    #
    wi
    vo
    cJ
    wral
    #
    wn
    #
    @6
    @7
    wn
    wa
    vo
    cJ
    wrex
    @4
    @3
    @9
    @0
    @1
    @2
    @3
    simpr3
    @4
    @8
    cA
    cB
    @0
    @1
    @2
    @8
    cA
    cB
    wceq
    wi
    @3
    cA
    cB
    vo
    cJ
    cX
    t1sep.1
    t1sep2
    3adant3r3
    necon3ad
    mpd
    @6
    @7
    vo
    cJ
    rexanali
    sylibr
end
