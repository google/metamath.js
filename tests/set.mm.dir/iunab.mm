include "cab.mm"
include "ciun.mm"
include "wrex.mm"
include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "nfcv.mm"
include "nfab1.mm"
include "nfiun.mm"
include "cleqf.mm"
include "abid.mm"
include "rexbii.mm"
include "eliun.mm"
include "3bitr4i.mm"
include "mpgbir.mm"

theorem iunab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint A y
  disjoint x y
  disjoint B x
  assert |- U_ x e. A { y | ph } = { y | E. x e. A ph }

  proof
    vx
    cA
    wph
    vy
    cab
    #
    ciun
    #
    wph
    vx
    cA
    wrex
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
    nfiun
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
    wrex
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
    rexbii
    vx
    @4
    cA
    @0
    eliun
    @2
    vy
    abid
    3bitr4i
    mpgbir
end
