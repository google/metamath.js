include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cicc.mm"
include "wss.mm"
include "icossicc.mm"
include "a1i.mm"
include "fssd.mm"

theorem fge0icoicc
  let wph: wff ph
  let cF: class F
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume fge0icoicc.1: |- ( ph -> F : X --> ( 0 [,) +oo ) )


  assert |- ( ph -> F : X --> ( 0 [,] +oo ) )

  proof
    wph
    cX
    cc0
    cpnf
    cico
    co
    #
    cc0
    cpnf
    cicc
    co
    #
    cF
    fge0icoicc.1
    @0
    @1
    wss
    wph
    cc0
    cpnf
    icossicc
    a1i
    fssd
end
