include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "cword.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "chash.mm"
include "cfz.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "wceq.mm"
include "wi.mm"
include "cwwlksn.mm"
include "w3a.mm"
include "wwlknbp1.mm"
include "simpl2.mm"
include "cfzo.mm"
include "peano2nn0.mm"
include "3ad2ant1.mm"
include "wb.mm"
include "eleq1.mm"
include "3ad2ant3.mm"
include "mpbird.mm"
include "adantr.mm"
include "cle.mm"
include "wbr.mm"
include "simpr.mm"
include "nn0re.mm"
include "lep1d.mm"
include "breq2.mm"
include "nn0p1elfzo.mm"
include "syl3anc.mm"
include "fz0add1fz1.mm"
include "syl2anc.mm"
include "jca.mm"
include "ex.mm"
include "syl.mm"
include "eleq2s.mm"
include "imp.mm"
include "swrd0fv0.mm"

theorem wwlksnextproplem1
  let cG: class G
  let cN: class N
  let cW: class W
  let cX: class X
  assume wwlksnextprop.x: |- X = ( ( N + 1 ) WWalksN G )


  assert |- ( ( W e. X /\ N e. NN0 ) -> ( ( W substr <. 0 , ( N + 1 ) >. ) ` 0 ) = ( W ` 0 ) )

  proof
    cW
    cX
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    cW
    cG
    cvtx
    cfv
    #
    cword
    wcel
    #
    cN
    c1
    caddc
    co
    #
    c1
    cW
    chash
    cfv
    #
    cfz
    co
    wcel
    #
    wa
    #
    cc0
    cW
    cc0
    @4
    cop
    csubstr
    co
    cfv
    cc0
    cW
    cfv
    wceq
    @0
    @1
    @7
    @1
    @7
    wi
    #
    cW
    @4
    cG
    cwwlksn
    co
    #
    cX
    cW
    @9
    wcel
    @4
    cn0
    wcel
    #
    @3
    @5
    @4
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    #
    @8
    cG
    @4
    cW
    wwlknbp1
    @13
    @1
    @7
    @13
    @1
    wa
    #
    @3
    @6
    @10
    @3
    @12
    @1
    simpl2
    @14
    @5
    cn0
    wcel
    #
    cN
    cc0
    @5
    cfzo
    co
    wcel
    #
    @6
    @13
    @15
    @1
    @13
    @15
    @11
    cn0
    wcel
    #
    @10
    @3
    @17
    @12
    @4
    peano2nn0
    3ad2ant1
    @12
    @10
    @15
    @17
    wb
    @3
    @5
    @11
    cn0
    eleq1
    3ad2ant3
    mpbird
    adantr
    #
    @14
    @1
    @15
    @4
    @5
    cle
    wbr
    #
    @16
    @13
    @1
    simpr
    @18
    @13
    @19
    @1
    @13
    @19
    @4
    @11
    cle
    wbr
    #
    @10
    @3
    @20
    @12
    @10
    @4
    @4
    nn0re
    lep1d
    3ad2ant1
    @12
    @10
    @19
    @20
    wb
    @3
    @5
    @11
    @4
    cle
    breq2
    3ad2ant3
    mpbird
    adantr
    cN
    @5
    nn0p1elfzo
    syl3anc
    @5
    cN
    fz0add1fz1
    syl2anc
    jca
    ex
    syl
    wwlksnextprop.x
    eleq2s
    imp
    @4
    @2
    cW
    swrd0fv0
    syl
end
