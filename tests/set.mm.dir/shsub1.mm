include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "cv.mm"
include "shsel1.mm"
include "ssrdv.mm"

theorem shsub1
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> A C_ ( A +H B ) )

  proof
    cA
    csh
    wcel
    cB
    csh
    wcel
    wa
    vx
    cA
    cA
    cB
    cph
    co
    cA
    cB
    vx
    cv
    shsel1
    ssrdv
end
