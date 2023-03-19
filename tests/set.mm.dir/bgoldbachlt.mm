include "c4.mm"
include "c1.mm"
include "cc0.mm"
include "cdc.mm"
include "c8.mm"
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
include "10nn.mm"
include "1nn0.mm"
include "8nn0.mm"
include "deccl.mm"
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
include "ax-bgbltosilva.mm"
include "syl3anc.mm"
include "ex.mm"
include "ralrimiva.mm"
include "jca.mm"
include "rspcedvd.mm"
include "ax-mp.mm"

theorem bgoldbachlt
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x

  disjoint m n
  disjoint k x
  assert |- E. m e. NN ( ( 4 x. ( ; 1 0 ^ ; 1 8 ) ) <_ m /\ A. n e. Even ( ( 4 < n /\ n < m ) -> n e. GoldbachEven ) )

  proof
    c4
    c1
    cc0
    cdc
    #
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
    @3
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
    @7
    @5
    clt
    wbr
    #
    wa
    #
    @7
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
    @2
    4nn
    @0
    cn
    wcel
    @1
    cn0
    wcel
    @2
    cn
    wcel
    10nn
    c1
    c8
    1nn0
    8nn0
    deccl
    @0
    @1
    nnexpcl
    mp2an
    nnmulcli
    @4
    @14
    @3
    @3
    cle
    wbr
    #
    @8
    @7
    @3
    clt
    wbr
    #
    wa
    #
    @11
    wi
    #
    vn
    ceven
    wral
    #
    wa
    #
    vm
    @3
    cn
    @4
    id
    @5
    @3
    wceq
    #
    @14
    @20
    wb
    @4
    @21
    @6
    @15
    @13
    @19
    @5
    @3
    @3
    cle
    breq2
    @21
    @12
    @18
    vn
    ceven
    @21
    @10
    @17
    @11
    @21
    @9
    @16
    @8
    @5
    @3
    @7
    clt
    breq2
    anbi2d
    imbi1d
    ralbidv
    anbi12d
    adantl
    @4
    @15
    @19
    @4
    @3
    @3
    nnre
    #
    leidd
    @4
    @18
    vn
    ceven
    @4
    @7
    ceven
    wcel
    #
    wa
    #
    @17
    @11
    @24
    @17
    wa
    @23
    @8
    @7
    @3
    cle
    wbr
    #
    @11
    @4
    @23
    @17
    simplr
    @24
    @8
    @16
    simprl
    @24
    @8
    @16
    @25
    @24
    @16
    @25
    wi
    #
    @8
    @23
    @7
    cr
    wcel
    @3
    cr
    wcel
    @26
    @4
    @23
    @7
    @7
    evenz
    zred
    @22
    @7
    @3
    ltle
    syl2anr
    a1d
    imp32
    @7
    ax-bgbltosilva
    syl3anc
    ex
    ralrimiva
    jca
    rspcedvd
    ax-mp
end
