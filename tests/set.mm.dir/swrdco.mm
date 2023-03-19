include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "wa.mm"
include "wf.mm"
include "w3a.mm"
include "cmin.mm"
include "cfzo.mm"
include "cop.mm"
include "csubstr.mm"
include "ccom.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "ffn.mm"
include "3ad2ant3.mm"
include "swrdvalfn.mm"
include "3expb.mm"
include "3adant3.mm"
include "swrdrn.mm"
include "fnco.mm"
include "syl3anc.mm"
include "wrdco.mm"
include "3adant2.mm"
include "simp2l.mm"
include "wi.mm"
include "lenco.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "expcom.mm"
include "com13.mm"
include "adantl.mm"
include "com12.mm"
include "3imp.mm"
include "cv.mm"
include "caddc.mm"
include "wceq.mm"
include "3anass.mm"
include "biimpri.mm"
include "swrdfv.mm"
include "fveq2d.mm"
include "sylan.mm"
include "wrdfn.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "elfzodifsumelfzo.mm"
include "3ad2ant2.mm"
include "imp.mm"
include "fvco2.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "ancoms.mm"
include "ex.mm"
include "3jca.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"

theorem swrdco
  let cA: class A
  let cB: class B
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  let vi: setvar i


  assert |- ( ( W e. Word A /\ ( M e. ( 0 ... N ) /\ N e. ( 0 ... ( # ` W ) ) ) /\ F : A --> B ) -> ( F o. ( W substr <. M , N >. ) ) = ( ( F o. W ) substr <. M , N >. ) )

  proof
    cW
    cA
    cword
    wcel
    #
    cM
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cc0
    cW
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    wa
    #
    cA
    cB
    cF
    wf
    #
    w3a
    #
    vi
    cc0
    cN
    cM
    cmin
    co
    cfzo
    co
    #
    cF
    cW
    cM
    cN
    cop
    #
    csubstr
    co
    #
    ccom
    #
    cF
    cW
    ccom
    #
    @9
    csubstr
    co
    #
    @7
    cF
    cA
    wfn
    #
    @10
    @8
    wfn
    #
    @10
    crn
    cA
    wss
    #
    @11
    @8
    wfn
    @6
    @0
    @14
    @5
    cA
    cB
    cF
    ffn
    3ad2ant3
    @0
    @5
    @15
    @6
    @0
    @1
    @4
    @15
    cW
    cM
    cN
    cA
    swrdvalfn
    3expb
    3adant3
    #
    @0
    @5
    @16
    @6
    @0
    @1
    @4
    @16
    cM
    cN
    cA
    cW
    swrdrn
    3expb
    3adant3
    cA
    @8
    cF
    @10
    fnco
    syl3anc
    @7
    @12
    cB
    cword
    wcel
    #
    @1
    cN
    cc0
    @12
    chash
    cfv
    #
    cfz
    co
    #
    wcel
    #
    @13
    @8
    wfn
    @0
    @6
    @18
    @5
    cA
    cB
    cF
    cW
    wrdco
    3adant2
    #
    @0
    @1
    @4
    @6
    simp2l
    #
    @0
    @5
    @6
    @21
    @5
    @0
    @6
    @21
    wi
    #
    @4
    @0
    @24
    wi
    #
    @1
    @6
    @0
    @4
    @21
    @0
    @6
    @4
    @21
    wi
    #
    @0
    @6
    wa
    #
    @4
    @21
    @27
    @3
    @20
    cN
    @27
    @2
    @19
    cc0
    cfz
    @27
    @19
    @2
    cA
    cB
    cF
    cW
    lenco
    #
    eqcomd
    oveq2d
    eleq2d
    biimpd
    expcom
    com13
    adantl
    com12
    3imp
    @12
    cM
    cN
    cB
    swrdvalfn
    syl3anc
    @7
    vi
    cv
    #
    @8
    wcel
    #
    wa
    #
    @29
    @10
    cfv
    #
    cF
    cfv
    #
    @29
    cM
    caddc
    co
    #
    @12
    cfv
    #
    @29
    @11
    cfv
    #
    @29
    @13
    cfv
    #
    @31
    @33
    @34
    cW
    cfv
    #
    cF
    cfv
    #
    @35
    @7
    @0
    @1
    @4
    w3a
    #
    @30
    @33
    @39
    wceq
    @0
    @5
    @40
    @6
    @40
    @0
    @5
    wa
    @0
    @1
    @4
    3anass
    biimpri
    3adant3
    @40
    @30
    wa
    @32
    @38
    cF
    cA
    cW
    cM
    cN
    @29
    swrdfv
    fveq2d
    sylan
    @31
    cW
    cc0
    @2
    cfzo
    co
    #
    wfn
    #
    @34
    @41
    wcel
    #
    @35
    @39
    wceq
    @7
    @42
    @30
    @0
    @5
    @42
    @6
    cA
    cW
    wrdfn
    3ad2ant1
    adantr
    @7
    @30
    @43
    @5
    @0
    @30
    @43
    wi
    @6
    @2
    @29
    cM
    cN
    elfzodifsumelfzo
    3ad2ant2
    imp
    @41
    cF
    cW
    @34
    fvco2
    syl2anc
    eqtr4d
    @7
    @15
    @30
    @36
    @33
    wceq
    @17
    @8
    cF
    @10
    @29
    fvco2
    sylan
    @7
    @18
    @1
    @21
    w3a
    @30
    @37
    @35
    wceq
    @7
    @18
    @1
    @21
    @22
    @23
    @0
    @5
    @6
    @21
    @5
    @0
    @24
    @4
    @25
    @1
    @6
    @0
    @4
    @21
    @6
    @0
    @26
    @6
    @0
    wa
    #
    @4
    @21
    @44
    @3
    @20
    cN
    @44
    @2
    @19
    cc0
    cfz
    @44
    @19
    @2
    @0
    @6
    @19
    @2
    wceq
    @28
    ancoms
    eqcomd
    oveq2d
    eleq2d
    biimpd
    ex
    com13
    adantl
    com12
    3imp
    3jca
    cB
    @12
    cM
    cN
    @29
    swrdfv
    sylan
    3eqtr4d
    eqfnfvd
end
