include "cnq.mm"
include "wcel.mm"
include "wa.mm"
include "cmq.mm"
include "co.mm"
include "cmpq.mm"
include "cerq.mm"
include "cfv.mm"
include "mulpqnq.mm"
include "cnpi.mm"
include "cxp.mm"
include "elpqn.mm"
include "mulpqf.mm"
include "fovcl.mm"
include "syl2an.mm"
include "nqercl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem mulclnq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. Q. /\ B e. Q. ) -> ( A .Q B ) e. Q. )

  proof
    cA
    cnq
    wcel
    #
    cB
    cnq
    wcel
    #
    wa
    #
    cA
    cB
    cmq
    co
    cA
    cB
    cmpq
    co
    #
    cerq
    cfv
    #
    cnq
    cA
    cB
    mulpqnq
    @2
    @3
    cnpi
    cnpi
    cxp
    #
    wcel
    #
    @4
    cnq
    wcel
    @0
    cA
    @5
    wcel
    cB
    @5
    wcel
    @6
    @1
    cA
    elpqn
    cB
    elpqn
    cA
    cB
    @5
    @5
    @5
    cmpq
    mulpqf
    fovcl
    syl2an
    @3
    nqercl
    syl
    eqeltrd
end
