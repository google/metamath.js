include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "c1.mm"
include "caddc.mm"
include "elfzo0.mm"
include "peano2nn0.mm"
include "3ad2ant1.mm"
include "peano2nn.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "nnre.mm"
include "1red.mm"
include "ltadd1.mm"
include "syl3an.mm"
include "mpbid.mm"
include "syl3anbrc.mm"
include "sylbi.mm"

theorem fzonn0p1p1
  let cI: class I
  let cN: class N


  assert |- ( I e. ( 0 ..^ N ) -> ( I + 1 ) e. ( 0 ..^ ( N + 1 ) ) )

  proof
    cI
    cc0
    cN
    cfzo
    co
    wcel
    cI
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    cI
    cN
    clt
    wbr
    #
    w3a
    #
    cI
    c1
    caddc
    co
    #
    cc0
    cN
    c1
    caddc
    co
    #
    cfzo
    co
    wcel
    #
    cI
    cN
    elfzo0
    @3
    @4
    cn0
    wcel
    #
    @5
    cn
    wcel
    #
    @4
    @5
    clt
    wbr
    #
    @6
    @0
    @1
    @7
    @2
    cI
    peano2nn0
    3ad2ant1
    @1
    @0
    @8
    @2
    cN
    peano2nn
    3ad2ant2
    @3
    @2
    @9
    @0
    @1
    @2
    simp3
    @0
    cI
    cr
    wcel
    @1
    cN
    cr
    wcel
    @2
    c1
    cr
    wcel
    @2
    @9
    wb
    cI
    nn0re
    cN
    nnre
    @2
    1red
    cI
    cN
    c1
    ltadd1
    syl3an
    mpbid
    @4
    @5
    elfzo0
    syl3anbrc
    sylbi
end
