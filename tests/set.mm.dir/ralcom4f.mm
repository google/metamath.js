include "cvv.mm"
include "wral.mm"
include "wal.mm"
include "nfcv.mm"
include "ralcomf.mm"
include "ralv.mm"
include "ralbii.mm"
include "3bitr3i.mm"

theorem ralcom4f
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume ralcom4f.1: |- F/_ y A

  disjoint x y
  assert |- ( A. x e. A A. y ph <-> A. y A. x e. A ph )

  proof
    wph
    vy
    cvv
    wral
    #
    vx
    cA
    wral
    wph
    vx
    cA
    wral
    #
    vy
    cvv
    wral
    wph
    vy
    wal
    #
    vx
    cA
    wral
    @1
    vy
    wal
    wph
    vx
    vy
    cA
    cvv
    ralcom4f.1
    vx
    cvv
    nfcv
    ralcomf
    @0
    @2
    vx
    cA
    wph
    vy
    ralv
    ralbii
    @1
    vy
    ralv
    3bitr3i
end
