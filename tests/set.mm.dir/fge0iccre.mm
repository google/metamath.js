include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cr.mm"
include "fge0iccico.mm"
include "wss.mm"
include "rge0ssre.mm"
include "a1i.mm"
include "fssd.mm"

theorem fge0iccre
  let wph: wff ph
  let cF: class F
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume fge0iccre.1: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume fge0iccre.2: |- ( ph -> -. +oo e. ran F )


  assert |- ( ph -> F : X --> RR )

  proof
    wph
    cX
    cc0
    cpnf
    cico
    co
    #
    cr
    cF
    wph
    cF
    cX
    fge0iccre.1
    fge0iccre.2
    fge0iccico
    @0
    cr
    wss
    wph
    rge0ssre
    a1i
    fssd
end
