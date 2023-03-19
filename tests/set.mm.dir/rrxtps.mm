include "wcel.mm"
include "crrx.mm"
include "cfv.mm"
include "cngp.mm"
include "ctps.mm"
include "rrxngp.mm"
include "ngptps.mm"
include "syl.mm"

theorem rrxtps
  let cI: class I
  let cV: class V
  let vk: setvar k
  let vx: setvar x


  assert |- ( I e. V -> ( RR^ ` I ) e. TopSp )

  proof
    cI
    cV
    wcel
    cI
    crrx
    cfv
    #
    cngp
    wcel
    @0
    ctps
    wcel
    cI
    cV
    rrxngp
    @0
    ngptps
    syl
end
