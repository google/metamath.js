include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wo.mm"
include "cmin.mm"
include "cn0.mm"
include "nneop.mm"
include "nnnn0.mm"
include "nn0o.mm"
include "syl2an.mm"
include "ex.mm"
include "orim2d.mm"
include "mpd.mm"

theorem nneom
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN -> ( ( N / 2 ) e. NN \/ ( ( N - 1 ) / 2 ) e. NN0 ) )

  proof
    cN
    cn
    wcel
    #
    cN
    c2
    cdiv
    co
    cn
    wcel
    #
    cN
    c1
    caddc
    co
    c2
    cdiv
    co
    #
    cn
    wcel
    #
    wo
    @1
    cN
    c1
    cmin
    co
    c2
    cdiv
    co
    cn0
    wcel
    #
    wo
    cN
    nneop
    @0
    @3
    @4
    @1
    @0
    @3
    @4
    @0
    cN
    cn0
    wcel
    @2
    cn0
    wcel
    @4
    @3
    cN
    nnnn0
    @2
    nnnn0
    cN
    nn0o
    syl2an
    ex
    orim2d
    mpd
end
