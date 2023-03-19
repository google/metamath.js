include "wcel.mm"
include "crrx.mm"
include "cfv.mm"
include "ccph.mm"
include "cngp.mm"
include "cbs.mm"
include "eqid.mm"
include "rrxcph.mm"
include "cphngp.mm"
include "syl.mm"

theorem rrxngp
  let cI: class I
  let cV: class V
  let vk: setvar k
  let vx: setvar x


  assert |- ( I e. V -> ( RR^ ` I ) e. NrmGrp )

  proof
    cI
    cV
    wcel
    cI
    crrx
    cfv
    #
    ccph
    wcel
    @0
    cngp
    wcel
    @0
    cbs
    cfv
    #
    @0
    cI
    cV
    @0
    eqid
    @1
    eqid
    rrxcph
    @0
    cphngp
    syl
end
