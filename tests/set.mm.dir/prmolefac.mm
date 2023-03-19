include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprime.mm"
include "cif.mm"
include "cprod.mm"
include "cprmo.mm"
include "cfv.mm"
include "cfa.mm"
include "cle.mm"
include "nfv.mm"
include "fzfid.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "1nn.mm"
include "a1i.mm"
include "ifcld.mm"
include "nnred.mm"
include "wceq.mm"
include "wo.mm"
include "cc0.mm"
include "wbr.mm"
include "wi.mm"
include "ifeqor.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "syl.mm"
include "breq2.mm"
include "syl5ibr.mm"
include "0le1.mm"
include "wb.mm"
include "adantr.mm"
include "mpbiri.mm"
include "ex.mm"
include "jaoi.mm"
include "ax-mp.mm"
include "leidd.mm"
include "breq1.mm"
include "nnge1d.mm"
include "fprodle.mm"
include "prmoval.mm"
include "fprodfac.mm"
include "3brtr4d.mm"

theorem prmolefac
  let cN: class N
  let vk: setvar k


  assert |- ( N e. NN0 -> ( #p ` N ) <_ ( ! ` N ) )

  proof
    cN
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    vk
    cv
    #
    cprime
    wcel
    #
    @2
    c1
    cif
    #
    vk
    cprod
    @1
    @2
    vk
    cprod
    cN
    cprmo
    cfv
    cN
    cfa
    cfv
    cle
    @0
    @1
    @4
    @2
    vk
    @0
    vk
    nfv
    @0
    c1
    cN
    fzfid
    @0
    @2
    @1
    wcel
    #
    wa
    #
    @4
    @6
    @3
    @2
    c1
    cn
    @5
    @2
    cn
    wcel
    #
    @0
    @2
    cN
    elfznn
    #
    adantl
    #
    c1
    cn
    wcel
    @6
    1nn
    a1i
    ifcld
    nnred
    @4
    @2
    wceq
    #
    @4
    c1
    wceq
    #
    wo
    #
    @6
    cc0
    @4
    cle
    wbr
    #
    wi
    #
    @3
    @2
    c1
    ifeqor
    #
    @10
    @14
    @11
    @6
    @13
    @10
    cc0
    @2
    cle
    wbr
    #
    @5
    @16
    @0
    @5
    @7
    @16
    @8
    @7
    @2
    @2
    nnnn0
    nn0ge0d
    syl
    adantl
    @4
    @2
    cc0
    cle
    breq2
    syl5ibr
    @11
    @6
    @13
    @11
    @6
    wa
    @13
    cc0
    c1
    cle
    wbr
    #
    0le1
    @11
    @13
    @17
    wb
    @6
    @4
    c1
    cc0
    cle
    breq2
    adantr
    mpbiri
    ex
    jaoi
    ax-mp
    @6
    @2
    @9
    nnred
    #
    @12
    @6
    @4
    @2
    cle
    wbr
    #
    wi
    #
    @15
    @10
    @20
    @11
    @6
    @19
    @10
    @2
    @2
    cle
    wbr
    @6
    @2
    @18
    leidd
    @4
    @2
    @2
    cle
    breq1
    syl5ibr
    @6
    @19
    @11
    c1
    @2
    cle
    wbr
    @6
    @2
    @9
    nnge1d
    @4
    c1
    @2
    cle
    breq1
    syl5ibr
    jaoi
    ax-mp
    fprodle
    vk
    cN
    prmoval
    cN
    vk
    fprodfac
    3brtr4d
end
