include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "c1.mm"
include "caddc.mm"
include "wo.mm"
include "nn0z.mm"
include "zeo.mm"
include "syl.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "simpr.mm"
include "cr.mm"
include "clt.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "2re.mm"
include "a1i.mm"
include "2pos.mm"
include "divge0.mm"
include "syl22anc.mm"
include "adantr.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "ex.mm"
include "peano2nn0.mm"
include "nn0red.mm"
include "1red.mm"
include "0le1.mm"
include "addge0d.mm"
include "orim12d.mm"
include "mpd.mm"

theorem nn0eo
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> ( ( N / 2 ) e. NN0 \/ ( ( N + 1 ) / 2 ) e. NN0 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    cN
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wo
    #
    @1
    cn0
    wcel
    #
    @4
    cn0
    wcel
    #
    wo
    @0
    cN
    cz
    wcel
    @6
    cN
    nn0z
    cN
    zeo
    syl
    @0
    @2
    @7
    @5
    @8
    @0
    @2
    @7
    @0
    @2
    wa
    @2
    cc0
    @1
    cle
    wbr
    #
    @7
    @0
    @2
    simpr
    @0
    @9
    @2
    @0
    cN
    cr
    wcel
    cc0
    cN
    cle
    wbr
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @9
    cN
    nn0re
    #
    cN
    nn0ge0
    #
    @10
    @0
    2re
    a1i
    #
    @11
    @0
    2pos
    a1i
    #
    cN
    c2
    divge0
    syl22anc
    adantr
    @1
    elnn0z
    sylanbrc
    ex
    @0
    @5
    @8
    @0
    @5
    wa
    @5
    cc0
    @4
    cle
    wbr
    #
    @8
    @0
    @5
    simpr
    @0
    @16
    @5
    @0
    @3
    cr
    wcel
    cc0
    @3
    cle
    wbr
    @10
    @11
    @16
    @0
    @3
    cN
    peano2nn0
    nn0red
    @0
    cN
    c1
    @12
    @0
    1red
    @13
    cc0
    c1
    cle
    wbr
    @0
    0le1
    a1i
    addge0d
    @14
    @15
    @3
    c2
    divge0
    syl22anc
    adantr
    @4
    elnn0z
    sylanbrc
    ex
    orim12d
    mpd
end
