include "cab.mm"
include "ciin.mm"
include "wral.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "nfcv.mm"
include "nfab1.mm"
include "nfiin.mm"
include "cleqf.mm"
include "abid.mm"
include "ralbii.mm"
include "cvv.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "3bitr4i.mm"
include "mpgbir.mm"

theorem iinab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A y
  disjoint x y
  assert |- |^|_ x e. A { y | ph } = { y | A. x e. A ph }

  proof
    vx
    cA
    wph
    vy
    cab
    #
    ciin
    #
    wph
    vx
    cA
    wral
    #
    vy
    cab
    #
    wceq
    vy
    cv
    #
    @1
    wcel
    #
    @4
    @3
    wcel
    #
    wb
    vy
    vy
    @1
    @3
    vx
    vy
    cA
    @0
    vy
    cA
    nfcv
    wph
    vy
    nfab1
    nfiin
    @2
    vy
    nfab1
    cleqf
    @4
    @0
    wcel
    #
    vx
    cA
    wral
    #
    @2
    @5
    @6
    @7
    wph
    vx
    cA
    wph
    vy
    abid
    ralbii
    @4
    cvv
    wcel
    @5
    @8
    wb
    vy
    vex
    vx
    @4
    cA
    @0
    cvv
    eliin
    ax-mp
    @2
    vy
    abid
    3bitr4i
    mpgbir
end
