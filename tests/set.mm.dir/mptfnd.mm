include "cvv.mm"
include "wcel.mm"
include "wral.mm"
include "cmpt.mm"
include "wfn.mm"
include "cv.mm"
include "ex.mm"
include "elex.mm"
include "syl6.mm"
include "ralrimi.mm"
include "mptfnf.mm"
include "sylib.mm"

theorem mptfnd
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  assume mptfnd.1: |- F/_ x A
  assume mptfnd.2: |- F/ x ph
  assume mptfnd.3: |- ( ( ph /\ x e. A ) -> B e. V )


  assert |- ( ph -> ( x e. A |-> B ) Fn A )

  proof
    wph
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
    wph
    @0
    vx
    cA
    mptfnd.2
    wph
    vx
    cv
    cA
    wcel
    #
    cB
    cV
    wcel
    #
    @0
    wph
    @1
    @2
    mptfnd.3
    ex
    cB
    cV
    elex
    syl6
    ralrimi
    vx
    cA
    cB
    mptfnd.1
    mptfnf
    sylib
end
