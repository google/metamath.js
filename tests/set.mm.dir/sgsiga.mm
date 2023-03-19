include "wcel.mm"
include "csigagen.mm"
include "cfv.mm"
include "cuni.mm"
include "csiga.mm"
include "crn.mm"
include "sigagensiga.mm"
include "elrnsiga.mm"
include "3syl.mm"

theorem sgsiga
  let wph: wff ph
  let cA: class A
  let cV: class V
  assume sgsiga.1: |- ( ph -> A e. V )


  assert |- ( ph -> ( sigaGen ` A ) e. U. ran sigAlgebra )

  proof
    wph
    cA
    cV
    wcel
    cA
    csigagen
    cfv
    #
    cA
    cuni
    #
    csiga
    cfv
    wcel
    @0
    csiga
    crn
    cuni
    wcel
    sgsiga.1
    cA
    cV
    sigagensiga
    @0
    @1
    elrnsiga
    3syl
end
