include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cprime.mm"
include "wa.mm"
include "cz.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wne.mm"
include "ccsh.mm"
include "wceq.mm"
include "w3a.mm"
include "creps.mm"
include "cv.mm"
include "cfzo.mm"
include "wral.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "simpr.mm"
include "adantr.mm"
include "simp1.mm"
include "adantl.mm"
include "simpr2.mm"
include "3jca.mm"
include "modprmn0modprm0.mm"
include "sylc.mm"
include "wi.mm"
include "cn0.mm"
include "elfzonn0.mm"
include "ad2antrr.mm"
include "simpl.mm"
include "anim12i.mm"
include "simpr3.mm"
include "anim1i.mm"
include "cshweqrep.mm"
include "weq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "fveq2.mm"
include "eqtrd.mm"
include "ex.mm"
include "rexlimiva.mm"
include "mpcom.mm"
include "ralrimiva.mm"
include "wb.mm"
include "repswsymballbi.mm"
include "mpbird.mm"

theorem cshwsidrepsw
  let cL: class L
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k


  assert |- ( ( W e. Word V /\ ( # ` W ) e. Prime ) -> ( ( L e. ZZ /\ ( L mod ( # ` W ) ) =/= 0 /\ ( W cyclShift L ) = W ) -> W = ( ( W ` 0 ) repeatS ( # ` W ) ) ) )

  proof
    cW
    cV
    cword
    wcel
    #
    cW
    chash
    cfv
    #
    cprime
    wcel
    #
    wa
    #
    cL
    cz
    wcel
    #
    cL
    @1
    cmo
    co
    cc0
    wne
    #
    cW
    cL
    ccsh
    co
    cW
    wceq
    #
    w3a
    #
    cW
    cc0
    cW
    cfv
    #
    @1
    creps
    co
    wceq
    #
    @3
    @7
    wa
    #
    @9
    vi
    cv
    #
    cW
    cfv
    #
    @8
    wceq
    #
    vi
    cc0
    @1
    cfzo
    co
    #
    wral
    #
    @10
    @13
    vi
    @14
    @11
    vj
    cv
    #
    cL
    cmul
    co
    #
    caddc
    co
    #
    @1
    cmo
    co
    #
    cc0
    wceq
    #
    vj
    @14
    wrex
    #
    @10
    @11
    @14
    wcel
    #
    wa
    #
    @13
    @23
    @2
    @4
    @5
    w3a
    #
    @22
    @21
    @10
    @24
    @22
    @10
    @2
    @4
    @5
    @3
    @2
    @7
    @0
    @2
    simpr
    adantr
    @7
    @4
    @3
    @4
    @5
    @6
    simp1
    #
    adantl
    @3
    @4
    @5
    @6
    simpr2
    3jca
    adantr
    @10
    @22
    simpr
    @1
    vj
    @11
    cL
    modprmn0modprm0
    sylc
    @20
    @23
    @13
    wi
    vj
    @14
    @16
    @14
    wcel
    #
    @20
    wa
    #
    @23
    @13
    @27
    @23
    wa
    #
    @12
    @19
    cW
    cfv
    #
    @8
    @28
    @16
    cn0
    wcel
    #
    @12
    @11
    vk
    cv
    #
    cL
    cmul
    co
    #
    caddc
    co
    #
    @1
    cmo
    co
    #
    cW
    cfv
    #
    wceq
    #
    vk
    cn0
    wral
    #
    @12
    @29
    wceq
    #
    @26
    @30
    @20
    @23
    @16
    @1
    elfzonn0
    ad2antrr
    @28
    @0
    @4
    wa
    #
    @6
    @22
    wa
    #
    @37
    @23
    @39
    @27
    @10
    @39
    @22
    @3
    @0
    @7
    @4
    @0
    @2
    simpl
    @25
    anim12i
    adantr
    adantl
    @23
    @40
    @27
    @10
    @6
    @22
    @3
    @4
    @5
    @6
    simpr3
    anim1i
    adantl
    vk
    @11
    cL
    cV
    cW
    cshweqrep
    sylc
    @36
    @38
    vk
    @16
    cn0
    vk
    vj
    weq
    #
    @35
    @29
    @12
    @41
    @34
    @19
    cW
    @41
    @33
    @18
    @1
    cmo
    @41
    @32
    @17
    @11
    caddc
    @31
    @16
    cL
    cmul
    oveq1
    oveq2d
    oveq1d
    fveq2d
    eqeq2d
    rspcva
    syl2anc
    @27
    @29
    @8
    wceq
    #
    @23
    @20
    @42
    @26
    @19
    cc0
    cW
    fveq2
    adantl
    adantr
    eqtrd
    ex
    rexlimiva
    mpcom
    ralrimiva
    @0
    @9
    @15
    wb
    @2
    @7
    vi
    cV
    cW
    repswsymballbi
    ad2antrr
    mpbird
    ex
end
