include "crab.mm"
include "ciin.mm"
include "cin.mm"
include "wral.mm"
include "wceq.mm"
include "c0.mm"
include "cvv.mm"
include "iineq1.mm"
include "0iin.mm"
include "syl6eq.mm"
include "ineq1d.mm"
include "incom.mm"
include "inv1.mm"
include "eqtri.mm"
include "rzal.mm"
include "rabid2.mm"
include "ralcom.mm"
include "bitr2i.mm"
include "sylib.mm"
include "eqtrd.mm"
include "wne.mm"
include "iinrab.mm"
include "wss.mm"
include "ssrab2.mm"
include "dfss.mm"
include "mpbi.mm"
include "syl6eqr.mm"
include "pm2.61ine.mm"

theorem iinrab2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A y
  disjoint x y
  disjoint A x
  disjoint B x
  disjoint B y
  assert |- ( |^|_ x e. A { y e. B | ph } i^i B ) = { y e. B | A. x e. A ph }

  proof
    vx
    cA
    wph
    vy
    cB
    crab
    #
    ciin
    #
    cB
    cin
    #
    wph
    vx
    cA
    wral
    #
    vy
    cB
    crab
    #
    wceq
    cA
    c0
    cA
    c0
    wceq
    #
    @2
    cB
    @4
    @5
    @2
    cvv
    cB
    cin
    #
    cB
    @5
    @1
    cvv
    cB
    @5
    @1
    vx
    c0
    @0
    ciin
    cvv
    vx
    cA
    c0
    @0
    iineq1
    vx
    @0
    0iin
    syl6eq
    ineq1d
    @6
    cB
    cvv
    cin
    cB
    cvv
    cB
    incom
    cB
    inv1
    eqtri
    syl6eq
    @5
    wph
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    cB
    @4
    wceq
    #
    @7
    vx
    cA
    rzal
    @9
    @3
    vy
    cB
    wral
    @8
    @3
    vy
    cB
    rabid2
    wph
    vy
    vx
    cB
    cA
    ralcom
    bitr2i
    sylib
    eqtrd
    cA
    c0
    wne
    #
    @2
    @4
    cB
    cin
    #
    @4
    @10
    @1
    @4
    cB
    wph
    vx
    vy
    cA
    cB
    iinrab
    ineq1d
    @4
    cB
    wss
    @4
    @11
    wceq
    @3
    vy
    cB
    ssrab2
    @4
    cB
    dfss
    mpbi
    syl6eqr
    pm2.61ine
end
