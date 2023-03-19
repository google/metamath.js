include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cmin.mm"
include "cfz.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "wss.mm"
include "wa.mm"
include "wn.mm"
include "wne.mm"
include "cn.mm"
include "eluz2nn.mm"
include "wo.mm"
include "wb.mm"
include "fzm1.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "biimpa.mm"
include "ord.mm"
include "sylan.mm"
include "cabs.mm"
include "cz.mm"
include "eluzelz.mm"
include "gcdid.mm"
include "syl.mm"
include "nnre.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "eqtrd.mm"
include "clt.mm"
include "wbr.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "cr.mm"
include "1re.mm"
include "ltne.mm"
include "mpan.mm"
include "eqnetrd.mm"
include "oveq1.mm"
include "neeq1d.mm"
include "syl5ibrcom.mm"
include "adantr.mm"
include "syld.mm"
include "necon4bd.mm"
include "ralrimiva.mm"
include "rabss.mm"
include "sylibr.mm"

theorem phibndlem
  let vx: setvar x
  let cN: class N

  disjoint N x
  assert |- ( N e. ( ZZ>= ` 2 ) -> { x e. ( 1 ... N ) | ( x gcd N ) = 1 } C_ ( 1 ... ( N - 1 ) ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    vx
    cv
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @1
    c1
    cN
    c1
    cmin
    co
    cfz
    co
    #
    wcel
    #
    wi
    #
    vx
    c1
    cN
    cfz
    co
    #
    wral
    @3
    vx
    @7
    crab
    @4
    wss
    @0
    @6
    vx
    @7
    @0
    @1
    @7
    wcel
    #
    wa
    #
    @5
    @2
    c1
    @9
    @5
    wn
    #
    @1
    cN
    wceq
    #
    @2
    c1
    wne
    #
    @0
    cN
    cn
    wcel
    #
    @8
    @10
    @11
    wi
    cN
    eluz2nn
    #
    @13
    @8
    wa
    @5
    @11
    @13
    @8
    @5
    @11
    wo
    #
    @8
    @15
    wb
    cN
    c1
    cuz
    cfv
    cn
    @1
    c1
    cN
    fzm1
    nnuz
    eleq2s
    biimpa
    ord
    sylan
    @0
    @11
    @12
    wi
    @8
    @0
    @12
    @11
    cN
    cN
    cgcd
    co
    #
    c1
    wne
    @0
    @16
    cN
    c1
    @0
    @16
    cN
    cabs
    cfv
    #
    cN
    @0
    cN
    cz
    wcel
    @16
    @17
    wceq
    c2
    cN
    eluzelz
    cN
    gcdid
    syl
    @0
    @13
    @17
    cN
    wceq
    @14
    @13
    cN
    cN
    nnre
    @13
    cN
    cN
    nnnn0
    nn0ge0d
    absidd
    syl
    eqtrd
    @0
    c1
    cN
    clt
    wbr
    #
    cN
    c1
    wne
    #
    @0
    @13
    @18
    cN
    eluz2b2
    simprbi
    c1
    cr
    wcel
    @18
    @19
    1re
    c1
    cN
    ltne
    mpan
    syl
    eqnetrd
    @11
    @2
    @16
    c1
    @1
    cN
    cN
    cgcd
    oveq1
    neeq1d
    syl5ibrcom
    adantr
    syld
    necon4bd
    ralrimiva
    @3
    vx
    @7
    @4
    rabss
    sylibr
end
