include "wceq.mm"
include "cfv.mm"
include "wcel.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"

theorem fveleq
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cF: class F


  assert |- ( A = B -> ( ( ph -> ( F ` A ) e. P ) <-> ( ph -> ( F ` B ) e. P ) ) )

  proof
    cA
    cB
    wceq
    #
    cA
    cF
    cfv
    #
    cP
    wcel
    cB
    cF
    cfv
    #
    cP
    wcel
    wph
    @0
    @1
    @2
    cP
    cA
    cB
    cF
    fveq2
    eleq1d
    imbi2d
end
