include "cn0.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cbc.mm"
include "cle.mm"
include "wbr.mm"
include "cdiv.mm"
include "2nn0.mm"
include "simpll.mm"
include "nn0mulcl.mm"
include "sylancr.mm"
include "simpr.mm"
include "nn0re.mm"
include "leidd.mm"
include "cc.mm"
include "wceq.mm"
include "nn0cn.mm"
include "cc0.mm"
include "wne.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "syl.mm"
include "breqtrrd.mm"
include "bcmono.mm"
include "syl3anc.mm"
include "cmin.mm"
include "simplr.mm"
include "bccmpl.mm"
include "syl2anc.mm"
include "caddc.mm"
include "nn0red.mm"
include "recnd.mm"
include "2timesd.mm"
include "zred.mm"
include "eluzle.mm"
include "adantl.mm"
include "leadd2dd.mm"
include "eqbrtrd.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "wb.mm"
include "nn0zd.mm"
include "zsubcld.mm"
include "eluz.mm"
include "wo.mm"
include "nn0z.mm"
include "adantr.mm"
include "uztric.mm"
include "mpjaodan.mm"

theorem bcmax
  let cK: class K
  let cN: class N


  assert |- ( ( N e. NN0 /\ K e. ZZ ) -> ( ( 2 x. N ) _C K ) <_ ( ( 2 x. N ) _C N ) )

  proof
    cN
    cn0
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    cN
    cK
    cuz
    cfv
    wcel
    #
    c2
    cN
    cmul
    co
    #
    cK
    cbc
    co
    #
    @4
    cN
    cbc
    co
    #
    cle
    wbr
    #
    cK
    cN
    cuz
    cfv
    wcel
    #
    @2
    @3
    wa
    #
    @4
    cn0
    wcel
    #
    @3
    cN
    @4
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    @7
    @9
    c2
    cn0
    wcel
    #
    @0
    @10
    2nn0
    @0
    @1
    @3
    simpll
    #
    c2
    cN
    nn0mulcl
    #
    sylancr
    @2
    @3
    simpr
    @9
    @0
    @12
    @14
    @0
    cN
    cN
    @11
    cle
    @0
    cN
    cN
    nn0re
    leidd
    @0
    cN
    cc
    wcel
    #
    @11
    cN
    wceq
    #
    cN
    nn0cn
    @16
    c2
    cc
    wcel
    c2
    cc0
    wne
    @17
    2cn
    2ne0
    cN
    c2
    divcan3
    mp3an23
    syl
    breqtrrd
    #
    syl
    cK
    cN
    @4
    bcmono
    syl3anc
    @2
    @8
    wa
    #
    @5
    @4
    @4
    cK
    cmin
    co
    #
    cbc
    co
    #
    @6
    cle
    @19
    @10
    @1
    @5
    @21
    wceq
    @19
    @13
    @0
    @10
    2nn0
    @0
    @1
    @8
    simpll
    #
    @15
    sylancr
    #
    @0
    @1
    @8
    simplr
    #
    cK
    @4
    bccmpl
    syl2anc
    @19
    @10
    cN
    @20
    cuz
    cfv
    wcel
    #
    @12
    @21
    @6
    cle
    wbr
    @23
    @19
    @25
    @20
    cN
    cle
    wbr
    #
    @19
    @26
    @4
    cN
    cK
    caddc
    co
    #
    cle
    wbr
    @19
    @4
    cN
    cN
    caddc
    co
    @27
    cle
    @19
    cN
    @19
    cN
    @19
    cN
    @22
    nn0red
    #
    recnd
    2timesd
    @19
    cN
    cK
    cN
    @28
    @19
    cK
    @24
    zred
    #
    @28
    @8
    cN
    cK
    cle
    wbr
    @2
    cN
    cK
    eluzle
    adantl
    leadd2dd
    eqbrtrd
    @19
    @4
    cK
    cN
    @19
    @4
    @23
    nn0red
    @29
    @28
    lesubaddd
    mpbird
    @19
    @20
    cz
    wcel
    cN
    cz
    wcel
    #
    @25
    @26
    wb
    @19
    @4
    cK
    @19
    @4
    @23
    nn0zd
    @24
    zsubcld
    @19
    cN
    @22
    nn0zd
    @20
    cN
    eluz
    syl2anc
    mpbird
    @19
    @0
    @12
    @22
    @18
    syl
    @20
    cN
    @4
    bcmono
    syl3anc
    eqbrtrd
    @2
    @1
    @30
    @3
    @8
    wo
    @0
    @1
    simpr
    @0
    @30
    @1
    cN
    nn0z
    adantr
    cK
    cN
    uztric
    syl2anc
    mpjaodan
end
