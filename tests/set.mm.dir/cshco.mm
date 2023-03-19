include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wf.mm"
include "w3a.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "ccsh.mm"
include "ccom.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "ffn.mm"
include "3ad2ant3.mm"
include "cshwfn.mm"
include "3adant3.mm"
include "cshwrn.mm"
include "fnco.mm"
include "syl3anc.mm"
include "wrdco.mm"
include "3adant2.mm"
include "simp2.mm"
include "syl2anc.mm"
include "wceq.mm"
include "lenco.mm"
include "oveq2d.mm"
include "fneq2d.mm"
include "mpbid.mm"
include "cv.mm"
include "wa.mm"
include "caddc.mm"
include "cmo.mm"
include "adantr.mm"
include "fveq2d.mm"
include "wrdfn.mm"
include "3ad2ant1.mm"
include "cn.mm"
include "elfzoelz.mm"
include "zaddcl.mm"
include "syl2anr.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "elfzo0.mm"
include "simp2bi.mm"
include "adantl.mm"
include "zmodfzo.mm"
include "wb.mm"
include "eleq1d.mm"
include "mpbird.mm"
include "fvco2.mm"
include "simpl1.mm"
include "simpr.mm"
include "cshwidxmod.mm"
include "3eqtr4rd.mm"
include "sylan.mm"
include "eqcomd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "3eqtr4d.mm"
include "eqfnfvd.mm"

theorem cshco
  let cA: class A
  let cB: class B
  let cF: class F
  let cN: class N
  let cW: class W
  let vi: setvar i


  assert |- ( ( W e. Word A /\ N e. ZZ /\ F : A --> B ) -> ( F o. ( W cyclShift N ) ) = ( ( F o. W ) cyclShift N ) )

  proof
    cW
    cA
    cword
    wcel
    #
    cN
    cz
    wcel
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
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cF
    cW
    cN
    ccsh
    co
    #
    ccom
    #
    cF
    cW
    ccom
    #
    cN
    ccsh
    co
    #
    @3
    cF
    cA
    wfn
    #
    @6
    @5
    wfn
    #
    @6
    crn
    cA
    wss
    #
    @7
    @5
    wfn
    @2
    @0
    @10
    @1
    cA
    cB
    cF
    ffn
    3ad2ant3
    @0
    @1
    @11
    @2
    cN
    cA
    cW
    cshwfn
    3adant3
    #
    @0
    @1
    @12
    @2
    cN
    cA
    cW
    cshwrn
    3adant3
    cA
    @5
    cF
    @6
    fnco
    syl3anc
    @3
    @9
    cc0
    @8
    chash
    cfv
    #
    cfzo
    co
    #
    wfn
    #
    @9
    @5
    wfn
    @3
    @8
    cB
    cword
    wcel
    #
    @1
    @16
    @0
    @2
    @17
    @1
    cA
    cB
    cF
    cW
    wrdco
    3adant2
    #
    @0
    @1
    @2
    simp2
    #
    cN
    cB
    @8
    cshwfn
    syl2anc
    @3
    @15
    @5
    @9
    @3
    @14
    @4
    cc0
    cfzo
    @0
    @2
    @14
    @4
    wceq
    #
    @1
    cA
    cB
    cF
    cW
    lenco
    3adant2
    #
    oveq2d
    fneq2d
    mpbid
    @3
    vi
    cv
    #
    @5
    wcel
    #
    wa
    #
    @22
    @6
    cfv
    #
    cF
    cfv
    #
    @22
    cN
    caddc
    co
    #
    @14
    cmo
    co
    #
    @8
    cfv
    #
    @22
    @7
    cfv
    #
    @22
    @9
    cfv
    #
    @24
    @28
    cW
    cfv
    #
    cF
    cfv
    #
    @27
    @4
    cmo
    co
    #
    cW
    cfv
    #
    cF
    cfv
    #
    @29
    @26
    @24
    @32
    @35
    cF
    @24
    @28
    @34
    cW
    @24
    @14
    @4
    @27
    cmo
    @3
    @20
    @23
    @21
    adantr
    oveq2d
    fveq2d
    fveq2d
    @24
    cW
    @5
    wfn
    #
    @28
    @5
    wcel
    #
    @29
    @33
    wceq
    @3
    @37
    @23
    @0
    @1
    @37
    @2
    cA
    cW
    wrdfn
    3ad2ant1
    adantr
    @24
    @38
    @34
    @5
    wcel
    #
    @24
    @27
    cz
    wcel
    #
    @4
    cn
    wcel
    #
    @39
    @23
    @22
    cz
    wcel
    @1
    @40
    @3
    @22
    cc0
    @4
    elfzoelz
    @19
    @22
    cN
    zaddcl
    syl2anr
    @23
    @41
    @3
    @23
    @22
    cn0
    wcel
    @41
    @22
    @4
    clt
    wbr
    @22
    @4
    elfzo0
    simp2bi
    adantl
    @27
    @4
    zmodfzo
    syl2anc
    @3
    @38
    @39
    wb
    @23
    @3
    @28
    @34
    @5
    @3
    @14
    @4
    @27
    cmo
    @21
    oveq2d
    eleq1d
    adantr
    mpbird
    @5
    cF
    cW
    @28
    fvco2
    syl2anc
    @24
    @0
    @1
    @23
    @26
    @36
    wceq
    @0
    @1
    @2
    @23
    simpl1
    @3
    @1
    @23
    @19
    adantr
    #
    @3
    @23
    simpr
    @0
    @1
    @23
    w3a
    @25
    @35
    cF
    @22
    cN
    cA
    cW
    cshwidxmod
    fveq2d
    syl3anc
    3eqtr4rd
    @3
    @11
    @23
    @30
    @26
    wceq
    @13
    @5
    cF
    @6
    @22
    fvco2
    sylan
    @24
    @17
    @1
    @22
    @15
    wcel
    #
    @31
    @29
    wceq
    @3
    @17
    @23
    @18
    adantr
    @42
    @3
    @23
    @43
    @3
    @5
    @15
    @22
    @3
    @4
    @14
    cc0
    cfzo
    @3
    @14
    @4
    @21
    eqcomd
    oveq2d
    eleq2d
    biimpa
    @22
    cN
    cB
    @8
    cshwidxmod
    syl3anc
    3eqtr4d
    eqfnfvd
end
