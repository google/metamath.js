include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wn.mm"
include "cep.mm"
include "wfr.mm"
include "zfregfr.mm"
include "efrn2lp.mm"
include "mpan.mm"
include "elex.mm"
include "anim12i.mm"
include "con3i.mm"
include "pm2.61i.mm"

theorem en2lp
  let cA: class A
  let cB: class B


  assert |- -. ( A e. B /\ B e. A )

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    cA
    cB
    wcel
    #
    cB
    cA
    wcel
    #
    wa
    #
    wn
    #
    cvv
    cep
    wfr
    @2
    @6
    cvv
    zfregfr
    cvv
    cA
    cB
    efrn2lp
    mpan
    @5
    @2
    @3
    @0
    @4
    @1
    cA
    cB
    elex
    cB
    cA
    elex
    anim12i
    con3i
    pm2.61i
end
