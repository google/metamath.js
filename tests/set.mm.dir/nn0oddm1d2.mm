include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cz.mm"
include "cmin.mm"
include "wb.mm"
include "nn0z.mm"
include "oddp1d2.mm"
include "syl.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "nn0re.mm"
include "1red.mm"
include "nn0ge0.mm"
include "0le1.mm"
include "a1i.mm"
include "addge0d.mm"
include "cr.mm"
include "clt.mm"
include "peano2nn0.mm"
include "nn0red.mm"
include "2re.mm"
include "2pos.mm"
include "ge0div.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "anim1i.mm"
include "ancomd.mm"
include "elnn0z.mm"
include "sylibr.mm"
include "ex.mm"
include "impbid1.mm"
include "nn0ob.mm"
include "3bitrd.mm"

theorem nn0oddm1d2
  let cN: class N


  assert |- ( N e. NN0 -> ( -. 2 || N <-> ( ( N - 1 ) / 2 ) e. NN0 ) )

  proof
    cN
    cn0
    wcel
    #
    c2
    cN
    cdvds
    wbr
    wn
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
    @3
    cn0
    wcel
    #
    cN
    c1
    cmin
    co
    c2
    cdiv
    co
    cn0
    wcel
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
    oddp1d2
    syl
    @0
    @4
    @5
    @0
    @4
    @5
    @0
    @4
    wa
    #
    @4
    cc0
    @3
    cle
    wbr
    #
    wa
    @5
    @6
    @7
    @4
    @0
    @7
    @4
    @0
    cc0
    @2
    cle
    wbr
    #
    @7
    @0
    cN
    c1
    cN
    nn0re
    @0
    1red
    cN
    nn0ge0
    cc0
    c1
    cle
    wbr
    @0
    0le1
    a1i
    addge0d
    @0
    @2
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
    @8
    @7
    wb
    @0
    @2
    cN
    peano2nn0
    nn0red
    @9
    @0
    2re
    a1i
    @10
    @0
    2pos
    a1i
    @2
    c2
    ge0div
    syl3anc
    mpbid
    anim1i
    ancomd
    @3
    elnn0z
    sylibr
    ex
    @3
    nn0z
    impbid1
    cN
    nn0ob
    3bitrd
end
