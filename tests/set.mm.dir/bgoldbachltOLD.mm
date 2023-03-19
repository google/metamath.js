include "c4.mm"
include "c10.mm"
include "c1.mm"
include "c8.mm"
include "cdc.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cgbe.mm"
include "wi.mm"
include "ceven.mm"
include "wral.mm"
include "wrex.mm"
include "4nn.mm"
include "cn0.mm"
include "10nnOLD.mm"
include "1nn0.mm"
include "8nn.mm"
include "decnncl.mm"
include "nnnn0i.mm"
include "nnexpcl.mm"
include "mp2an.mm"
include "nnmulcli.mm"
include "id.mm"
include "wceq.mm"
include "wb.mm"
include "breq2.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "adantl.mm"
include "nnre.mm"
include "leidd.mm"
include "simplr.mm"
include "simprl.mm"
include "cr.mm"
include "evenz.mm"
include "zred.mm"
include "ltle.mm"
include "syl2anr.mm"
include "a1d.mm"
include "imp32.mm"
include "ax-bgbltosilvaOLD.mm"
include "syl3anc.mm"
include "ex.mm"
include "ralrimiva.mm"
include "jca.mm"
include "rspcedvd.mm"
include "ax-mp.mm"

theorem bgoldbachltOLD
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x

  disjoint m n
  disjoint k x
  assert |- E. m e. NN ( ( 4 x. ( 10 ^ ; 1 8 ) ) <_ m /\ A. n e. Even ( ( 4 < n /\ n < m ) -> n e. GoldbachEven ) )

  proof
    c4
    c10
    c1
    c8
    cdc
    #
    cexp
    co
    #
    cmul
    co
    #
    cn
    wcel
    #
    @2
    vm
    cv
    #
    cle
    wbr
    #
    c4
    vn
    cv
    #
    clt
    wbr
    #
    @6
    @4
    clt
    wbr
    #
    wa
    #
    @6
    cgbe
    wcel
    #
    wi
    #
    vn
    ceven
    wral
    #
    wa
    #
    vm
    cn
    wrex
    c4
    @1
    4nn
    c10
    cn
    wcel
    @0
    cn0
    wcel
    @1
    cn
    wcel
    10nnOLD
    @0
    c1
    c8
    1nn0
    8nn
    decnncl
    nnnn0i
    c10
    @0
    nnexpcl
    mp2an
    nnmulcli
    @3
    @13
    @2
    @2
    cle
    wbr
    #
    @7
    @6
    @2
    clt
    wbr
    #
    wa
    #
    @10
    wi
    #
    vn
    ceven
    wral
    #
    wa
    #
    vm
    @2
    cn
    @3
    id
    @4
    @2
    wceq
    #
    @13
    @19
    wb
    @3
    @20
    @5
    @14
    @12
    @18
    @4
    @2
    @2
    cle
    breq2
    @20
    @11
    @17
    vn
    ceven
    @20
    @9
    @16
    @10
    @20
    @8
    @15
    @7
    @4
    @2
    @6
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    anbi12d
    adantl
    @3
    @14
    @18
    @3
    @2
    @2
    nnre
    #
    leidd
    @3
    @17
    vn
    ceven
    @3
    @6
    ceven
    wcel
    #
    wa
    #
    @16
    @10
    @23
    @16
    wa
    @22
    @7
    @6
    @2
    cle
    wbr
    #
    @10
    @3
    @22
    @16
    simplr
    @23
    @7
    @15
    simprl
    @23
    @7
    @15
    @24
    @23
    @15
    @24
    wi
    #
    @7
    @22
    @6
    cr
    wcel
    @2
    cr
    wcel
    @25
    @3
    @22
    @6
    @6
    evenz
    zred
    @21
    @6
    @2
    ltle
    syl2anr
    a1d
    imp32
    @6
    ax-bgbltosilvaOLD
    syl3anc
    ex
    ralrimiva
    jca
    rspcedvd
    ax-mp
end
