include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cn0.mm"
include "cmin.mm"
include "cn.mm"
include "wne.mm"
include "wa.mm"
include "wi.mm"
include "eluz2b3.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "nnnn0.mm"
include "nn0o1gt2.mm"
include "sylan.mm"
include "eqneqall.mm"
include "a1d.mm"
include "cz.mm"
include "cc0.mm"
include "nn0z.mm"
include "peano2zm.mm"
include "syl.mm"
include "ad2antlr.mm"
include "cmul.mm"
include "2cn.mm"
include "mulid2i.mm"
include "nnre.mm"
include "ltp1d.mm"
include "adantr.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "peano2nn.mm"
include "nnred.mm"
include "lttr.mm"
include "syl3anc.mm"
include "expdimp.mm"
include "mpd.mm"
include "syl5eqbr.mm"
include "wb.mm"
include "1red.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltmuldiv.mm"
include "mpbid.mm"
include "rehalfcld.mm"
include "posdifd.mm"
include "adantlr.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "cc.mm"
include "nncn.mm"
include "xp1d2m1eqxm1d2.mm"
include "eleq1d.mm"
include "expcom.mm"
include "jaoi.mm"
include "mpcom.mm"
include "impancom.mm"
include "sylbi.mm"
include "imp.mm"

theorem nno
  let cN: class N


  assert |- ( ( N e. ( ZZ>= ` 2 ) /\ ( ( N + 1 ) / 2 ) e. NN0 ) -> ( ( N - 1 ) / 2 ) e. NN )

  proof
    cN
    c2
    cuz
    cfv
    wcel
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
    #
    cn
    wcel
    #
    @0
    cN
    cn
    wcel
    #
    cN
    c1
    wne
    #
    wa
    @3
    @5
    wi
    cN
    eluz2b3
    @6
    @3
    @7
    @5
    cN
    c1
    wceq
    #
    c2
    cN
    clt
    wbr
    #
    wo
    #
    @6
    @3
    wa
    #
    @7
    @5
    wi
    #
    @6
    cN
    cn0
    wcel
    @3
    @10
    cN
    nnnn0
    cN
    nn0o1gt2
    sylan
    @8
    @11
    @12
    wi
    @9
    @8
    @12
    @11
    @5
    cN
    c1
    eqneqall
    a1d
    @11
    @9
    @12
    @11
    @9
    wa
    #
    @5
    @7
    @13
    @2
    c1
    cmin
    co
    #
    cn
    wcel
    #
    @5
    @13
    @14
    cz
    wcel
    #
    cc0
    @14
    clt
    wbr
    #
    @15
    @3
    @16
    @6
    @9
    @3
    @2
    cz
    wcel
    @16
    @2
    nn0z
    @2
    peano2zm
    syl
    ad2antlr
    @6
    @9
    @17
    @3
    @6
    @9
    wa
    #
    c1
    @2
    clt
    wbr
    #
    @17
    @18
    c1
    c2
    cmul
    co
    #
    @1
    clt
    wbr
    #
    @19
    @18
    @20
    c2
    @1
    clt
    c2
    2cn
    mulid2i
    @18
    cN
    @1
    clt
    wbr
    #
    c2
    @1
    clt
    wbr
    #
    @6
    @22
    @9
    @6
    cN
    cN
    nnre
    #
    ltp1d
    adantr
    @6
    @9
    @22
    @23
    @6
    c2
    cr
    wcel
    #
    cN
    cr
    wcel
    @1
    cr
    wcel
    #
    @9
    @22
    wa
    @23
    wi
    @25
    @6
    2re
    a1i
    @24
    @6
    @1
    cN
    peano2nn
    nnred
    #
    c2
    cN
    @1
    lttr
    syl3anc
    expdimp
    mpd
    syl5eqbr
    @18
    c1
    cr
    wcel
    @26
    @25
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @21
    @19
    wb
    @18
    1red
    #
    @6
    @26
    @9
    @27
    adantr
    @29
    @18
    @25
    @28
    2re
    2pos
    pm3.2i
    a1i
    c1
    @1
    c2
    ltmuldiv
    syl3anc
    mpbid
    @18
    c1
    @2
    @30
    @6
    @2
    cr
    wcel
    @9
    @6
    @1
    @27
    rehalfcld
    adantr
    posdifd
    mpbid
    adantlr
    @14
    elnnz
    sylanbrc
    @11
    @15
    @5
    wb
    #
    @9
    @6
    @31
    @3
    @6
    @14
    @4
    cn
    @6
    cN
    cc
    wcel
    @14
    @4
    wceq
    cN
    nncn
    cN
    xp1d2m1eqxm1d2
    syl
    eleq1d
    adantr
    adantr
    mpbid
    a1d
    expcom
    jaoi
    mpcom
    impancom
    sylbi
    imp
end
