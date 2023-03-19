include "kl.mm"
include "kt.mm"
include "ke.mm"
include "kbr.mm"
include "tal.mm"
include "kc.mm"
include "hb.mm"
include "ax-cb2.mm"
include "wtru.mm"
include "eqtru.mm"
include "eqcomi.mm"
include "leq.mm"
include "ax-cb1.mm"
include "wl.mm"
include "alval.mm"
include "a1i.mm"
include "mpbir.mm"

theorem alrimiv
  param hal: type al
  param vx: var x
  param ta: term A
  param tr: term R
  assume alrimiv.1: |- R |= A

  disjoint R x
  disjoint al x
  assert |- R |= ( ! \ x : al . A )

  proof
    hal
    vx
    ta
    kl
    #
    hal
    vx
    kt
    kl
    ke
    kbr
    #
    tal
    @0
    kc
    #
    tr
    hal
    hb
    vx
    ta
    kt
    tr
    ta
    tr
    alrimiv.1
    ax-cb2
    #
    hb
    kt
    ta
    tr
    wtru
    ta
    tr
    alrimiv.1
    eqtru
    eqcomi
    leq
    @2
    @1
    ke
    kbr
    tr
    ta
    tr
    alrimiv.1
    ax-cb1
    hal
    vx
    @0
    hal
    hb
    vx
    ta
    @3
    wl
    alval
    a1i
    mpbir
end
