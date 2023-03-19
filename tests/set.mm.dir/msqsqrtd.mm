include "csqrt.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "sqrtcld.mm"
include "sqvald.mm"
include "sqsqrtd.mm"
include "eqtr3d.mm"

theorem msqsqrtd
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( ( sqrt ` A ) x. ( sqrt ` A ) ) = A )

  proof
    wph
    cA
    csqrt
    cfv
    #
    c2
    cexp
    co
    @0
    @0
    cmul
    co
    cA
    wph
    @0
    wph
    cA
    abscld.1
    sqrtcld
    sqvald
    wph
    cA
    abscld.1
    sqsqrtd
    eqtr3d
end
