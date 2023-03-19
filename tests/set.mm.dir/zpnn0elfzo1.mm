include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "c1.mm"
include "cfzo.mm"
include "zpnn0elfzo.mm"
include "cc.mm"
include "zcn.mm"
include "adantr.mm"
include "nn0cn.mm"
include "adantl.mm"
include "1cnd.mm"
include "addassd.mm"
include "oveq2d.mm"
include "eleqtrd.mm"

theorem zpnn0elfzo1
  let cN: class N
  let cZ: class Z


  assert |- ( ( Z e. ZZ /\ N e. NN0 ) -> ( Z + N ) e. ( Z ..^ ( Z + ( N + 1 ) ) ) )

  proof
    cZ
    cz
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cZ
    cN
    caddc
    co
    #
    cZ
    @3
    c1
    caddc
    co
    #
    cfzo
    co
    cZ
    cZ
    cN
    c1
    caddc
    co
    caddc
    co
    #
    cfzo
    co
    cN
    cZ
    zpnn0elfzo
    @2
    @4
    @5
    cZ
    cfzo
    @2
    cZ
    cN
    c1
    @0
    cZ
    cc
    wcel
    @1
    cZ
    zcn
    adantr
    @1
    cN
    cc
    wcel
    @0
    cN
    nn0cn
    adantl
    @2
    1cnd
    addassd
    oveq2d
    eleqtrd
end
