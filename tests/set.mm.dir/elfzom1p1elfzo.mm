include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "wcel.mm"
include "cn.mm"
include "caddc.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "wi.mm"
include "elfzo0.mm"
include "wa.mm"
include "peano2nn0.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simpr.mm"
include "cr.mm"
include "nn0re.mm"
include "1red.mm"
include "nnre.mm"
include "adantl.mm"
include "ltaddsubd.mm"
include "biimprd.mm"
include "impancom.mm"
include "3adant2.mm"
include "imp.mm"
include "syl3anbrc.mm"
include "ex.mm"
include "sylbi.mm"
include "impcom.mm"

theorem elfzom1p1elfzo
  let cN: class N
  let cX: class X


  assert |- ( ( N e. NN /\ X e. ( 0 ..^ ( N - 1 ) ) ) -> ( X + 1 ) e. ( 0 ..^ N ) )

  proof
    cX
    cc0
    cN
    c1
    cmin
    co
    #
    cfzo
    co
    wcel
    #
    cN
    cn
    wcel
    #
    cX
    c1
    caddc
    co
    #
    cc0
    cN
    cfzo
    co
    wcel
    #
    @1
    cX
    cn0
    wcel
    #
    @0
    cn
    wcel
    #
    cX
    @0
    clt
    wbr
    #
    w3a
    #
    @2
    @4
    wi
    cX
    @0
    elfzo0
    @8
    @2
    @4
    @8
    @2
    wa
    @3
    cn0
    wcel
    #
    @2
    @3
    cN
    clt
    wbr
    #
    @4
    @8
    @9
    @2
    @5
    @6
    @9
    @7
    cX
    peano2nn0
    3ad2ant1
    adantr
    @8
    @2
    simpr
    @8
    @2
    @10
    @5
    @7
    @2
    @10
    wi
    @6
    @5
    @2
    @7
    @10
    @5
    @2
    wa
    #
    @10
    @7
    @11
    cX
    c1
    cN
    @5
    cX
    cr
    wcel
    @2
    cX
    nn0re
    adantr
    @11
    1red
    @2
    cN
    cr
    wcel
    @5
    cN
    nnre
    adantl
    ltaddsubd
    biimprd
    impancom
    3adant2
    imp
    @3
    cN
    elfzo0
    syl3anbrc
    ex
    sylbi
    impcom
end
