include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "shsub1.mm"
include "shscom.mm"
include "sseqtrd.mm"

theorem shsub2
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A e. SH /\ B e. SH ) -> A C_ ( B +H A ) )

  proof
    cA
    csh
    wcel
    cB
    csh
    wcel
    wa
    cA
    cA
    cB
    cph
    co
    cB
    cA
    cph
    co
    cA
    cB
    shsub1
    cA
    cB
    shscom
    sseqtrd
end
