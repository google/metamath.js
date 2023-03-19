include "kl.mm"
include "tv.mm"
include "kc.mm"
include "tex.mm"
include "ax-id.mm"
include "ke.mm"
include "kbr.mm"
include "hb.mm"
include "beta.mm"
include "a1i.mm"
include "mpbir.mm"
include "wl.mm"
include "wv.mm"
include "ax4e.mm"
include "syl.mm"

theorem 19.8a
  param hal: type al
  param vx: var x
  param ta: term A
  assume 19.8a.1: |- A : bool


  assert |- A |= ( ? \ x : al . A )

  proof
    ta
    hal
    vx
    ta
    kl
    #
    hal
    vx
    tv
    #
    kc
    #
    tex
    @0
    kc
    ta
    @2
    ta
    ta
    19.8a.1
    ax-id
    @2
    ta
    ke
    kbr
    ta
    19.8a.1
    hal
    hb
    vx
    ta
    19.8a.1
    beta
    a1i
    mpbir
    hal
    @1
    @0
    hal
    hb
    vx
    ta
    19.8a.1
    wl
    hal
    vx
    wv
    ax4e
    syl
end
