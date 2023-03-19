include "cn.mm"
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
include "wb.mm"
include "nnz.mm"
include "oddp1d2.mm"
include "syl.mm"
include "wa.mm"
include "cc0.mm"
include "clt.mm"
include "peano2nn.mm"
include "nnred.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nnre.mm"
include "1red.mm"
include "nngt0.mm"
include "0lt1.mm"
include "addgt0d.mm"
include "2pos.mm"
include "divgt0d.mm"
include "anim1i.mm"
include "ancomd.mm"
include "elnnz.mm"
include "sylibr.mm"
include "ex.mm"
include "impbid1.mm"
include "bitrd.mm"

theorem nnoddm1d2
  let cN: class N


  assert |- ( N e. NN -> ( -. 2 || N <-> ( ( N + 1 ) / 2 ) e. NN ) )

  proof
    cN
    cn
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
    cn
    wcel
    #
    @0
    cN
    cz
    wcel
    @1
    @4
    wb
    cN
    nnz
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
    clt
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
    @2
    c2
    @0
    @2
    cN
    peano2nn
    nnred
    c2
    cr
    wcel
    @0
    2re
    a1i
    @0
    cN
    c1
    cN
    nnre
    @0
    1red
    cN
    nngt0
    cc0
    c1
    clt
    wbr
    @0
    0lt1
    a1i
    addgt0d
    cc0
    c2
    clt
    wbr
    @0
    2pos
    a1i
    divgt0d
    anim1i
    ancomd
    @3
    elnnz
    sylibr
    ex
    @3
    nnz
    impbid1
    bitrd
end
