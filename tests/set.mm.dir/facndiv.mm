include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "cfa.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cz.mm"
include "wn.mm"
include "cr.mm"
include "nnre.mm"
include "recnz.mm"
include "sylan.mm"
include "ad2ant2lr.mm"
include "cmin.mm"
include "facdiv.mm"
include "3expa.mm"
include "nnzd.mm"
include "adantrl.mm"
include "zsubcl.mm"
include "ex.mm"
include "syl5com.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "faccl.mm"
include "nncnd.mm"
include "peano2cn.mm"
include "syl.mm"
include "ad2antrr.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "ad2antlr.mm"
include "divsubdir.mm"
include "syl3anc.mm"
include "ax-1cn.mm"
include "pncan2.mm"
include "sylancl.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "mtod.mm"

theorem facndiv
  let cM: class M
  let cN: class N


  assert |- ( ( ( M e. NN0 /\ N e. NN ) /\ ( 1 < N /\ N <_ M ) ) -> -. ( ( ( ! ` M ) + 1 ) / N ) e. ZZ )

  proof
    cM
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    c1
    cN
    clt
    wbr
    #
    cN
    cM
    cle
    wbr
    #
    wa
    #
    wa
    #
    cM
    cfa
    cfv
    #
    c1
    caddc
    co
    #
    cN
    cdiv
    co
    #
    cz
    wcel
    #
    c1
    cN
    cdiv
    co
    #
    cz
    wcel
    #
    @1
    @3
    @12
    wn
    #
    @0
    @4
    @1
    cN
    cr
    wcel
    @3
    @13
    cN
    nnre
    cN
    recnz
    sylan
    ad2ant2lr
    @6
    @10
    @9
    @7
    cN
    cdiv
    co
    #
    cmin
    co
    #
    cz
    wcel
    #
    @12
    @6
    @14
    cz
    wcel
    #
    @10
    @16
    @2
    @4
    @17
    @3
    @2
    @4
    wa
    @14
    @0
    @1
    @4
    @14
    cn
    wcel
    cM
    cN
    facdiv
    3expa
    nnzd
    adantrl
    @10
    @17
    @16
    @9
    @14
    zsubcl
    ex
    syl5com
    @6
    @15
    @11
    cz
    @6
    @8
    @7
    cmin
    co
    #
    cN
    cdiv
    co
    #
    @15
    @11
    @6
    @8
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    cN
    cc
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    #
    @19
    @15
    wceq
    @0
    @20
    @1
    @5
    @0
    @21
    @20
    @0
    @7
    cM
    faccl
    nncnd
    #
    @7
    peano2cn
    syl
    ad2antrr
    @0
    @21
    @1
    @5
    @25
    ad2antrr
    @1
    @24
    @0
    @5
    @1
    @22
    @23
    cN
    nncn
    cN
    nnne0
    jca
    ad2antlr
    @8
    @7
    cN
    divsubdir
    syl3anc
    @0
    @19
    @11
    wceq
    @1
    @5
    @0
    @18
    c1
    cN
    cdiv
    @0
    @21
    c1
    cc
    wcel
    @18
    c1
    wceq
    @25
    ax-1cn
    @7
    c1
    pncan2
    sylancl
    oveq1d
    ad2antrr
    eqtr3d
    eleq1d
    sylibd
    mtod
end
