include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "sqsqrtd.mm"
include "sq0id.mm"
include "eqtr3d.mm"

theorem sqr00d
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )
  assume sqrt00d.2: |- ( ph -> ( sqrt ` A ) = 0 )


  assert |- ( ph -> A = 0 )

  proof
    wph
    cA
    csqrt
    cfv
    #
    c2
    cexp
    co
    cA
    cc0
    wph
    cA
    abscld.1
    sqsqrtd
    wph
    @0
    sqrt00d.2
    sq0id
    eqtr3d
end
