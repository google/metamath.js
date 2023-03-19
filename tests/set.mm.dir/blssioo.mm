include "cbl.mm"
include "cfv.mm"
include "crn.mm"
include "cioo.mm"
include "cv.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "cxr.mm"
include "wrex.mm"
include "cr.mm"
include "cxmt.mm"
include "wb.mm"
include "rexmet.mm"
include "blrn.mm"
include "ax-mp.mm"
include "wa.mm"
include "cpnf.mm"
include "cmnf.mm"
include "w3o.mm"
include "elxr.mm"
include "cmin.mm"
include "caddc.mm"
include "bl2ioo.mm"
include "resubcl.mm"
include "readdcl.mm"
include "rexr.mm"
include "cxp.mm"
include "wfn.mm"
include "cpw.mm"
include "wf.mm"
include "ioof.mm"
include "ffn.mm"
include "fnovrn.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "cme.mm"
include "remet.mm"
include "blpnf.mm"
include "mpan.mm"
include "sylan9eqr.mm"
include "ioomax.mm"
include "ioorebas.mm"
include "eqeltrri.mm"
include "syl6eqel.mm"
include "c0.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "0xr.mm"
include "nltmnf.mm"
include "wne.mm"
include "mnfxr.mm"
include "xbln0.mm"
include "mp3an13.mm"
include "necon1bbid.mm"
include "mpbii.mm"
include "iooid.mm"
include "3jaodan.mm"
include "sylan2b.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "ssriv.mm"

theorem blssioo
  let cD: class D
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  assume remet.1: |- D = ( ( abs o. - ) |` ( RR X. RR ) )


  assert |- ran ( ball ` D ) C_ ran (,)

  proof
    vz
    cD
    cbl
    cfv
    #
    crn
    #
    cioo
    crn
    #
    vz
    cv
    #
    @1
    wcel
    #
    @3
    vy
    cv
    #
    vr
    cv
    #
    @0
    co
    #
    wceq
    #
    vr
    cxr
    wrex
    vy
    cr
    wrex
    #
    @3
    @2
    wcel
    #
    cD
    cr
    cxmt
    cfv
    wcel
    #
    @4
    @9
    wb
    cD
    remet.1
    rexmet
    #
    vy
    @3
    cD
    cr
    vr
    blrn
    ax-mp
    @8
    @10
    vy
    vr
    cr
    cxr
    @5
    cr
    wcel
    #
    @6
    cxr
    wcel
    #
    wa
    @10
    @8
    @7
    @2
    wcel
    #
    @14
    @13
    @6
    cr
    wcel
    #
    @6
    cpnf
    wceq
    #
    @6
    cmnf
    wceq
    #
    w3o
    @15
    @6
    elxr
    @13
    @16
    @15
    @17
    @18
    @13
    @16
    wa
    #
    @7
    @5
    @6
    cmin
    co
    #
    @5
    @6
    caddc
    co
    #
    cioo
    co
    #
    @2
    @5
    @6
    cD
    remet.1
    bl2ioo
    @19
    @20
    cr
    wcel
    #
    @21
    cr
    wcel
    #
    @22
    @2
    wcel
    #
    @5
    @6
    resubcl
    @5
    @6
    readdcl
    @23
    @20
    cxr
    wcel
    #
    @21
    cxr
    wcel
    #
    @25
    @24
    @20
    rexr
    @21
    rexr
    cioo
    cxr
    cxr
    cxp
    #
    wfn
    #
    @26
    @27
    @25
    @28
    cr
    cpw
    #
    cioo
    wf
    @29
    ioof
    @28
    @30
    cioo
    ffn
    ax-mp
    cxr
    cxr
    @20
    @21
    cioo
    fnovrn
    mp3an1
    syl2an
    syl2anc
    eqeltrd
    @13
    @17
    wa
    @7
    cr
    @2
    @17
    @13
    @7
    @5
    cpnf
    @0
    co
    #
    cr
    @6
    cpnf
    @5
    @0
    oveq2
    cD
    cr
    cme
    cfv
    wcel
    @13
    @31
    cr
    wceq
    cD
    remet.1
    remet
    cD
    @5
    cr
    blpnf
    mpan
    sylan9eqr
    cmnf
    cpnf
    cioo
    co
    cr
    @2
    ioomax
    cmnf
    cpnf
    ioorebas
    eqeltrri
    syl6eqel
    @13
    @18
    wa
    @7
    c0
    @2
    @18
    @13
    @7
    @5
    cmnf
    @0
    co
    #
    c0
    @6
    cmnf
    @5
    @0
    oveq2
    @13
    cc0
    cmnf
    clt
    wbr
    #
    wn
    #
    @32
    c0
    wceq
    cc0
    cxr
    wcel
    @34
    0xr
    cc0
    nltmnf
    ax-mp
    @13
    @33
    @32
    c0
    @11
    @13
    cmnf
    cxr
    wcel
    @32
    c0
    wne
    @33
    wb
    @12
    mnfxr
    cD
    @5
    cmnf
    cr
    xbln0
    mp3an13
    necon1bbid
    mpbii
    sylan9eqr
    cc0
    cc0
    cioo
    co
    c0
    @2
    cc0
    iooid
    cc0
    cc0
    ioorebas
    eqeltrri
    syl6eqel
    3jaodan
    sylan2b
    @3
    @7
    @2
    eleq1
    syl5ibrcom
    rexlimivv
    sylbi
    ssriv
end
