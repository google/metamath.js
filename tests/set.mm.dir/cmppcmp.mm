include "ccmp.mm"
include "wcel.mm"
include "ctop.mm"
include "cuni.mm"
include "cv.mm"
include "wceq.mm"
include "cref.mm"
include "wbr.mm"
include "cpw.mm"
include "clocfin.mm"
include "cfv.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cpcmp.mm"
include "cmptop.mm"
include "cfn.mm"
include "ccref.mm"
include "wa.mm"
include "cmpcref.mm"
include "eleq2i.mm"
include "eqid.mm"
include "iscref.mm"
include "bitri.mm"
include "simprbi.mm"
include "simprl.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "ad3antrrr.mm"
include "simprd.mm"
include "simplr.mm"
include "simprr.mm"
include "refbas.mm"
include "syl.mm"
include "eqtrd.mm"
include "finlocfin.mm"
include "syl3anc.mm"
include "elind.mm"
include "jca.mm"
include "ex.mm"
include "reximdv2.mm"
include "a2d.mm"
include "ralimdva.mm"
include "mpd.mm"
include "ispcmp.mm"
include "sylanbrc.mm"

theorem cmppcmp
  let cJ: class J
  let vy: setvar y
  let vz: setvar z


  assert |- ( J e. Comp -> J e. Paracomp )

  proof
    cJ
    ccmp
    wcel
    #
    cJ
    ctop
    wcel
    #
    cJ
    cuni
    #
    vy
    cv
    #
    cuni
    #
    wceq
    #
    vz
    cv
    #
    @3
    cref
    wbr
    #
    vz
    cJ
    cpw
    #
    cJ
    clocfin
    cfv
    #
    cin
    #
    wrex
    #
    wi
    #
    vy
    @8
    wral
    #
    cJ
    cpcmp
    wcel
    #
    cJ
    cmptop
    #
    @0
    @5
    @7
    vz
    @8
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vy
    @8
    wral
    #
    @13
    @0
    @1
    @19
    @0
    cJ
    cfn
    ccref
    #
    wcel
    @1
    @19
    wa
    ccmp
    @20
    cJ
    cmpcref
    eleq2i
    vy
    vz
    cfn
    cJ
    @2
    @2
    eqid
    #
    iscref
    bitri
    simprbi
    @0
    @18
    @12
    vy
    @8
    @0
    @3
    @8
    wcel
    #
    wa
    #
    @5
    @17
    @11
    @23
    @5
    @17
    @11
    wi
    @23
    @5
    wa
    #
    @7
    @7
    vz
    @16
    @10
    @24
    @6
    @16
    wcel
    #
    @7
    wa
    #
    @6
    @10
    wcel
    #
    @7
    wa
    @24
    @26
    wa
    #
    @27
    @7
    @28
    @8
    @9
    @6
    @28
    @6
    @8
    wcel
    #
    @6
    cfn
    wcel
    #
    @28
    @25
    @29
    @30
    wa
    @24
    @25
    @7
    simprl
    @6
    @8
    cfn
    elin
    sylib
    #
    simpld
    @28
    @1
    @30
    @2
    @6
    cuni
    #
    wceq
    @6
    @9
    wcel
    @0
    @1
    @22
    @5
    @26
    @15
    ad3antrrr
    @28
    @29
    @30
    @31
    simprd
    @28
    @2
    @4
    @32
    @23
    @5
    @26
    simplr
    @28
    @7
    @4
    @32
    wceq
    @24
    @25
    @7
    simprr
    #
    @6
    @3
    @32
    @4
    @32
    eqid
    #
    @4
    eqid
    refbas
    syl
    eqtrd
    @6
    cJ
    @2
    @32
    @21
    @34
    finlocfin
    syl3anc
    elind
    @33
    jca
    ex
    reximdv2
    ex
    a2d
    ralimdva
    mpd
    @14
    cJ
    @9
    ccref
    wcel
    @1
    @13
    wa
    cJ
    ispcmp
    vy
    vz
    @9
    cJ
    @2
    @21
    iscref
    bitri
    sylanbrc
end
