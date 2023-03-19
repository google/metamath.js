include "cn.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cle.mm"
include "c1.mm"
include "nncn.mm"
include "mulid1d.mm"
include "wbr.mm"
include "nnge1.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "wb.mm"
include "1red.mm"
include "nnre.mm"
include "nngt0.mm"
include "lemul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "eqbrtrrd.mm"
include "cc.mm"
include "wceq.mm"
include "sqval.mm"
include "syl.mm"
include "breqtrrd.mm"

theorem nnlesq
  let cN: class N


  assert |- ( N e. NN -> N <_ ( N ^ 2 ) )

  proof
    cN
    cn
    wcel
    #
    cN
    cN
    cN
    cmul
    co
    #
    cN
    c2
    cexp
    co
    #
    cle
    @0
    cN
    c1
    cmul
    co
    #
    cN
    @1
    cle
    @0
    cN
    cN
    nncn
    #
    mulid1d
    @0
    c1
    cN
    cle
    wbr
    #
    @3
    @1
    cle
    wbr
    #
    cN
    nnge1
    @0
    c1
    cr
    wcel
    cN
    cr
    wcel
    #
    @7
    cc0
    cN
    clt
    wbr
    @5
    @6
    wb
    @0
    1red
    cN
    nnre
    #
    @8
    cN
    nngt0
    c1
    cN
    cN
    lemul2
    syl112anc
    mpbid
    eqbrtrrd
    @0
    cN
    cc
    wcel
    @2
    @1
    wceq
    @4
    cN
    sqval
    syl
    breqtrrd
end
