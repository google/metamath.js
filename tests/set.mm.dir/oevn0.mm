include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "coe.mm"
include "co.mm"
include "cvv.mm"
include "cv.mm"
include "comu.mm"
include "cmpt.mm"
include "c1o.mm"
include "crdg.mm"
include "cfv.mm"
include "wceq.mm"
include "wn.mm"
include "wb.mm"
include "wne.mm"
include "on0eln0.mm"
include "df-ne.mm"
include "syl6bb.mm"
include "adantr.mm"
include "cdif.mm"
include "cif.mm"
include "oev.mm"
include "iffalse.mm"
include "sylan9eq.mm"
include "ex.mm"
include "sylbid.mm"
include "imp.mm"

theorem oevn0
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( ( A e. On /\ B e. On ) /\ (/) e. A ) -> ( A ^o B ) = ( rec ( ( x e. _V |-> ( x .o A ) ) , 1o ) ` B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    c0
    cA
    wcel
    #
    cA
    cB
    coe
    co
    #
    cB
    vx
    cvv
    vx
    cv
    cA
    comu
    co
    cmpt
    c1o
    crdg
    cfv
    #
    wceq
    #
    @2
    @3
    cA
    c0
    wceq
    #
    wn
    #
    @6
    @0
    @3
    @8
    wb
    @1
    @0
    @3
    cA
    c0
    wne
    @8
    cA
    on0eln0
    cA
    c0
    df-ne
    syl6bb
    adantr
    @2
    @8
    @6
    @2
    @8
    @4
    @7
    c1o
    cB
    cdif
    #
    @5
    cif
    @5
    vx
    cA
    cB
    oev
    @7
    @9
    @5
    iffalse
    sylan9eq
    ex
    sylbid
    imp
end
