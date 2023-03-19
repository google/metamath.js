include "wcel.mm"
include "wral.mm"
include "cvv.mm"
include "cmpt.mm"
include "wfn.mm"
include "elex.mm"
include "ralimi.mm"
include "mptfnf.mm"
include "sylib.mm"

theorem fnmptf
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y
  assume mptfnf.0: |- F/_ x A


  assert |- ( A. x e. A B e. V -> ( x e. A |-> B ) Fn A )

  proof
    cB
    cV
    wcel
    #
    vx
    cA
    wral
    cB
    cvv
    wcel
    #
    vx
    cA
    wral
    vx
    cA
    cB
    cmpt
    cA
    wfn
    @0
    @1
    vx
    cA
    cB
    cV
    elex
    ralimi
    vx
    cA
    cB
    mptfnf.0
    mptfnf
    sylib
end
