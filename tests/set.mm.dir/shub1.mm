include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cph.mm"
include "co.mm"
include "chj.mm"
include "shsub1.mm"
include "shslej.mm"
include "sstrd.mm"

theorem shub1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. SH /\ B e. SH ) -> A C_ ( A vH B ) )

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
    cA
    cB
    chj
    co
    cA
    cB
    shsub1
    cA
    cB
    shslej
    sstrd
end
