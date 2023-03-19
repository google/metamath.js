include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cr.mm"
include "caddc.mm"
include "co.mm"
include "cin.mm"
include "cdif.mm"
include "cun.mm"
include "inundif.mm"
include "fveq2i.mm"
include "c0.mm"
include "wceq.mm"
include "inmbl.mm"
include "adantr.mm"
include "difmbl.mm"
include "indifcom.mm"
include "difin0.mm"
include "ineq2i.mm"
include "in0.mm"
include "eqtri.mm"
include "a1i.mm"
include "covol.mm"
include "mblvol.mm"
include "syl.mm"
include "wss.mm"
include "inss1.mm"
include "mblss.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "eqeltrrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "difssd.mm"
include "volun.mm"
include "syl32anc.mm"
include "syl5eqr.mm"
include "oveq1d.mm"
include "recnd.mm"
include "simprr.mm"
include "addassd.mm"
include "undif1.mm"
include "simplr.mm"
include "incom.mm"
include "disjdif.mm"
include "syl5reqr.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem volinun
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. dom vol /\ B e. dom vol ) /\ ( ( vol ` A ) e. RR /\ ( vol ` B ) e. RR ) ) -> ( ( vol ` A ) + ( vol ` B ) ) = ( ( vol ` ( A i^i B ) ) + ( vol ` ( A u. B ) ) ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cvol
    cfv
    #
    cr
    wcel
    #
    cB
    cvol
    cfv
    #
    cr
    wcel
    #
    wa
    #
    wa
    #
    @4
    @6
    caddc
    co
    cA
    cB
    cin
    #
    cvol
    cfv
    #
    cA
    cB
    cdif
    #
    cvol
    cfv
    #
    caddc
    co
    #
    @6
    caddc
    co
    @11
    @13
    @6
    caddc
    co
    #
    caddc
    co
    @11
    cA
    cB
    cun
    #
    cvol
    cfv
    #
    caddc
    co
    @9
    @4
    @14
    @6
    caddc
    @9
    @4
    @10
    @12
    cun
    #
    cvol
    cfv
    #
    @14
    @18
    cA
    cvol
    cA
    cB
    inundif
    fveq2i
    @9
    @10
    @0
    wcel
    #
    @12
    @0
    wcel
    #
    @10
    @12
    cin
    #
    c0
    wceq
    #
    @11
    cr
    wcel
    @13
    cr
    wcel
    #
    @19
    @14
    wceq
    @3
    @20
    @8
    cA
    cB
    inmbl
    adantr
    #
    @3
    @21
    @8
    cA
    cB
    difmbl
    adantr
    #
    @23
    @9
    @22
    cA
    @10
    cB
    cdif
    #
    cin
    #
    c0
    @10
    cA
    cB
    indifcom
    @28
    cA
    c0
    cin
    c0
    @27
    c0
    cA
    cA
    cB
    difin0
    ineq2i
    cA
    in0
    eqtri
    eqtri
    a1i
    @9
    @11
    @10
    covol
    cfv
    #
    cr
    @9
    @20
    @11
    @29
    wceq
    @25
    @10
    mblvol
    syl
    @9
    @10
    cA
    wss
    #
    cA
    cr
    wss
    #
    cA
    covol
    cfv
    #
    cr
    wcel
    #
    @29
    cr
    wcel
    @30
    @9
    cA
    cB
    inss1
    a1i
    @1
    @31
    @2
    @8
    cA
    mblss
    ad2antrr
    #
    @9
    @4
    @32
    cr
    @1
    @4
    @32
    wceq
    @2
    @8
    cA
    mblvol
    ad2antrr
    @3
    @5
    @7
    simprl
    eqeltrrd
    #
    @10
    cA
    ovolsscl
    syl3anc
    eqeltrd
    #
    @9
    @13
    @12
    covol
    cfv
    #
    cr
    @9
    @21
    @13
    @37
    wceq
    @26
    @12
    mblvol
    syl
    @9
    @12
    cA
    wss
    @31
    @33
    @37
    cr
    wcel
    @9
    cA
    cB
    difssd
    @34
    @35
    @12
    cA
    ovolsscl
    syl3anc
    eqeltrd
    #
    @10
    @12
    volun
    syl32anc
    syl5eqr
    oveq1d
    @9
    @11
    @13
    @6
    @9
    @11
    @36
    recnd
    @9
    @13
    @38
    recnd
    @9
    @6
    @3
    @5
    @7
    simprr
    #
    recnd
    addassd
    @9
    @15
    @17
    @11
    caddc
    @9
    @17
    @12
    cB
    cun
    #
    cvol
    cfv
    #
    @15
    @40
    @16
    cvol
    cA
    cB
    undif1
    fveq2i
    @9
    @21
    @2
    @12
    cB
    cin
    #
    c0
    wceq
    #
    @24
    @7
    @41
    @15
    wceq
    @26
    @1
    @2
    @8
    simplr
    @43
    @9
    @42
    cB
    @12
    cin
    c0
    @12
    cB
    incom
    cB
    cA
    disjdif
    eqtri
    a1i
    @38
    @39
    @12
    cB
    volun
    syl32anc
    syl5reqr
    oveq2d
    3eqtrd
end
