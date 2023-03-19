include "cv.mm"
include "wcel.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "cico.mm"
include "uzubioo2.mm"
include "wss.mm"
include "wi.mm"
include "ioossico.mm"
include "ssrexv.mm"
include "ax-mp.mm"
include "ralimi.mm"
include "syl.mm"

theorem uzubico2
  let wph: wff ph
  let vx: setvar x
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  assume uzubico2.1: |- ( ph -> M e. ZZ )
  assume uzubico2.2: |- Z = ( ZZ>= ` M )

  disjoint M k
  disjoint Z k
  disjoint Z x
  disjoint k x
  assert |- ( ph -> A. x e. RR E. k e. ( x [,) +oo ) k e. Z )

  proof
    wph
    vk
    cv
    cZ
    wcel
    #
    vk
    vx
    cv
    #
    cpnf
    cioo
    co
    #
    wrex
    #
    vx
    cr
    wral
    @0
    vk
    @1
    cpnf
    cico
    co
    #
    wrex
    #
    vx
    cr
    wral
    wph
    vx
    vk
    cM
    cZ
    uzubico2.1
    uzubico2.2
    uzubioo2
    @3
    @5
    vx
    cr
    @2
    @4
    wss
    @3
    @5
    wi
    @1
    cpnf
    ioossico
    @0
    vk
    @2
    @4
    ssrexv
    ax-mp
    ralimi
    syl
end
