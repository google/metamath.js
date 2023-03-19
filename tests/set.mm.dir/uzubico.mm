include "cv.mm"
include "wcel.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "wrex.mm"
include "cico.mm"
include "uzubioo.mm"
include "wss.mm"
include "wi.mm"
include "ioossico.mm"
include "ssrexv.mm"
include "ax-mp.mm"
include "syl.mm"

theorem uzubico
  let wph: wff ph
  let vk: setvar k
  let cM: class M
  let cX: class X
  let cZ: class Z
  assume uzubico.1: |- ( ph -> M e. ZZ )
  assume uzubico.2: |- Z = ( ZZ>= ` M )
  assume uzubico.3: |- ( ph -> X e. RR )

  disjoint M k
  disjoint X k
  disjoint Z k
  assert |- ( ph -> E. k e. ( X [,) +oo ) k e. Z )

  proof
    wph
    vk
    cv
    cZ
    wcel
    #
    vk
    cX
    cpnf
    cioo
    co
    #
    wrex
    #
    @0
    vk
    cX
    cpnf
    cico
    co
    #
    wrex
    #
    wph
    vk
    cM
    cX
    cZ
    uzubico.1
    uzubico.2
    uzubico.3
    uzubioo
    @1
    @3
    wss
    @2
    @4
    wi
    cX
    cpnf
    ioossico
    @0
    vk
    @1
    @3
    ssrexv
    ax-mp
    syl
end
