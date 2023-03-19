include "wfn.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "crn.mm"
include "jca.mm"
include "fnfvelrn.mm"
include "syl.mm"

theorem fnfvelrnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume fnfvelrnd.1: |- ( ph -> F Fn A )
  assume fnfvelrnd.2: |- ( ph -> B e. A )


  assert |- ( ph -> ( F ` B ) e. ran F )

  proof
    wph
    cF
    cA
    wfn
    #
    cB
    cA
    wcel
    #
    wa
    cB
    cF
    cfv
    cF
    crn
    wcel
    wph
    @0
    @1
    fnfvelrnd.1
    fnfvelrnd.2
    jca
    cA
    cB
    cF
    fnfvelrn
    syl
end
