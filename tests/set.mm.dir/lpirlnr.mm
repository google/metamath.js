include "clpir.mm"
include "wcel.mm"
include "crg.mm"
include "cv.mm"
include "crsp.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "clidl.mm"
include "wral.mm"
include "clnr.mm"
include "lpirring.mm"
include "clpidl.mm"
include "wa.mm"
include "csn.mm"
include "wb.mm"
include "eqid.mm"
include "islpidl.mm"
include "syl.mm"
include "biimpa.mm"
include "snelpwi.mm"
include "adantl.mm"
include "snfi.mm"
include "a1i.mm"
include "elind.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylancl.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "islpir.mm"
include "simprbi.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "islnr2.mm"
include "sylanbrc.mm"

theorem lpirlnr
  let cR: class R
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( R e. LPIR -> R e. LNoeR )

  proof
    cR
    clpir
    wcel
    #
    cR
    crg
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cR
    crsp
    cfv
    #
    cfv
    #
    wceq
    #
    vb
    cR
    cbs
    cfv
    #
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    va
    cR
    clidl
    cfv
    #
    wral
    #
    cR
    clnr
    wcel
    cR
    lpirring
    #
    @0
    @12
    @10
    va
    cR
    clpidl
    cfv
    #
    wral
    @0
    @10
    va
    @14
    @0
    @2
    @14
    wcel
    #
    wa
    #
    @2
    vc
    cv
    #
    csn
    #
    @4
    cfv
    #
    wceq
    #
    vc
    @7
    wrex
    #
    @10
    @0
    @15
    @21
    @0
    @1
    @15
    @21
    wb
    @13
    @7
    @14
    cR
    vc
    @2
    @4
    @14
    eqid
    #
    @4
    eqid
    #
    @7
    eqid
    #
    islpidl
    syl
    biimpa
    @16
    @20
    @10
    vc
    @7
    @16
    @17
    @7
    wcel
    #
    wa
    #
    @10
    @20
    @19
    @5
    wceq
    #
    vb
    @9
    wrex
    #
    @26
    @18
    @9
    wcel
    @19
    @19
    wceq
    #
    @28
    @26
    @8
    cfn
    @18
    @25
    @18
    @8
    wcel
    @16
    @17
    @7
    snelpwi
    adantl
    @18
    cfn
    wcel
    @26
    @17
    snfi
    a1i
    elind
    @19
    eqid
    @27
    @29
    vb
    @18
    @9
    @3
    @18
    wceq
    @5
    @19
    @19
    @3
    @18
    @4
    fveq2
    eqeq2d
    rspcev
    sylancl
    @20
    @6
    @27
    vb
    @9
    @2
    @19
    @5
    eqeq1
    rexbidv
    syl5ibrcom
    rexlimdva
    mpd
    ralrimiva
    @0
    @10
    va
    @11
    @14
    @0
    @1
    @11
    @14
    wceq
    @14
    cR
    @11
    @22
    @11
    eqid
    #
    islpir
    simprbi
    raleqdv
    mpbird
    @7
    cR
    @11
    vb
    va
    @4
    @24
    @30
    @23
    islnr2
    sylanbrc
end
