include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "cn0.mm"
include "wnel.mm"
include "cr.mm"
include "0re.mm"
include "wn.mm"
include "nnel.mm"
include "cneg.mm"
include "df-neg.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "cle.mm"
include "wbr.mm"
include "nn0ge0.mm"
include "nnre.mm"
include "le0neg1d.mm"
include "clt.mm"
include "wi.mm"
include "nngt0.mm"
include "0red.mm"
include "ltnled.mm"
include "pm2.21.mm"
include "syl6bi.mm"
include "mpd.mm"
include "sylbird.mm"
include "syl5.mm"
include "syl5bi.mm"
include "mt4i.mm"

theorem 0mnnnnn0
  let cN: class N


  assert |- ( N e. NN -> ( 0 - N ) e/ NN0 )

  proof
    cN
    cn
    wcel
    #
    cc0
    cN
    cmin
    co
    #
    cn0
    wnel
    #
    cc0
    cr
    wcel
    #
    0re
    @2
    wn
    @1
    cn0
    wcel
    #
    @0
    @3
    wn
    #
    @1
    cn0
    nnel
    @4
    cN
    cneg
    #
    cn0
    wcel
    #
    @0
    @5
    @1
    @6
    cn0
    @6
    @1
    cN
    df-neg
    eqcomi
    eleq1i
    @7
    cc0
    @6
    cle
    wbr
    #
    @0
    @5
    @6
    nn0ge0
    @0
    @8
    cN
    cc0
    cle
    wbr
    #
    @5
    @0
    cN
    cN
    nnre
    #
    le0neg1d
    @0
    cc0
    cN
    clt
    wbr
    #
    @9
    @5
    wi
    #
    cN
    nngt0
    @0
    @11
    @9
    wn
    @12
    @0
    cc0
    cN
    @0
    0red
    @10
    ltnled
    @9
    @5
    pm2.21
    syl6bi
    mpd
    sylbird
    syl5
    syl5bi
    syl5bi
    mt4i
end
