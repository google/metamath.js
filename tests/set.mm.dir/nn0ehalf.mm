include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "wb.mm"
include "nn0z.mm"
include "evend2.mm"
include "syl.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "nn0ge0.mm"
include "cr.mm"
include "clt.mm"
include "nn0re.mm"
include "2re.mm"
include "a1i.mm"
include "2pos.mm"
include "ge0div.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "anim1i.mm"
include "ancomd.mm"
include "elnn0z.mm"
include "sylibr.mm"
include "ex.mm"
include "sylbid.mm"
include "imp.mm"

theorem nn0ehalf
  let cN: class N


  assert |- ( ( N e. NN0 /\ 2 || N ) -> ( N / 2 ) e. NN0 )

  proof
    cN
    cn0
    wcel
    #
    c2
    cN
    cdvds
    wbr
    #
    cN
    c2
    cdiv
    co
    #
    cn0
    wcel
    #
    @0
    @1
    @2
    cz
    wcel
    #
    @3
    @0
    cN
    cz
    wcel
    @1
    @4
    wb
    cN
    nn0z
    cN
    evend2
    syl
    @0
    @4
    @3
    @0
    @4
    wa
    #
    @4
    cc0
    @2
    cle
    wbr
    #
    wa
    @3
    @5
    @6
    @4
    @0
    @6
    @4
    @0
    cc0
    cN
    cle
    wbr
    #
    @6
    cN
    nn0ge0
    @0
    cN
    cr
    wcel
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @7
    @6
    wb
    cN
    nn0re
    @8
    @0
    2re
    a1i
    @9
    @0
    2pos
    a1i
    cN
    c2
    ge0div
    syl3anc
    mpbid
    anim1i
    ancomd
    @2
    elnn0z
    sylibr
    ex
    sylbid
    imp
end
