include "cphtpc.mm"
include "cfv.mm"
include "wbr.mm"
include "ctop.mm"
include "wcel.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "cphtpy.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "df-br.mm"
include "cdm.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wa.mm"
include "copab.mm"
include "df-phtpc.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "sylbi.mm"
include "cntop2.mm"
include "3ad2ant1.mm"
include "wceq.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "vex.mm"
include "prss.mm"
include "syl6bbr.mm"
include "fveq2.mm"
include "oveqd.mm"
include "neeq1d.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "cxp.mm"
include "ovex.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "breqd.mm"
include "oveq12.mm"
include "eqid.mm"
include "brab2a.mm"
include "df-3an.mm"
include "bitr4i.mm"
include "syl6bb.mm"
include "pm5.21nii.mm"

theorem isphtpc
  let cF: class F
  let cG: class G
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j


  assert |- ( F ( ~=ph ` J ) G <-> ( F e. ( II Cn J ) /\ G e. ( II Cn J ) /\ ( F ( PHtpy ` J ) G ) =/= (/) ) )

  proof
    cF
    cG
    cJ
    cphtpc
    cfv
    #
    wbr
    #
    cJ
    ctop
    wcel
    #
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    cG
    @3
    wcel
    #
    cF
    cG
    cJ
    cphtpy
    cfv
    #
    co
    #
    c0
    wne
    #
    w3a
    #
    @1
    cF
    cG
    cop
    #
    @0
    wcel
    #
    @2
    cF
    cG
    @0
    df-br
    @11
    cphtpc
    cdm
    ctop
    cJ
    vj
    ctop
    vf
    cv
    #
    vg
    cv
    #
    cpr
    #
    cii
    vj
    cv
    #
    ccn
    co
    #
    wss
    #
    @12
    @13
    @15
    cphtpy
    cfv
    #
    co
    #
    c0
    wne
    #
    wa
    #
    vf
    vg
    copab
    #
    cphtpc
    vj
    vf
    vg
    df-phtpc
    #
    dmmptss
    @10
    cJ
    cphtpc
    elfvdm
    sseldi
    sylbi
    @4
    @5
    @2
    @8
    cF
    cii
    cJ
    cntop2
    3ad2ant1
    @2
    @1
    cF
    cG
    @12
    @3
    wcel
    @13
    @3
    wcel
    wa
    #
    @12
    @13
    @6
    co
    #
    c0
    wne
    #
    wa
    #
    vf
    vg
    copab
    #
    wbr
    #
    @9
    @2
    @0
    @28
    cF
    cG
    vj
    cJ
    @22
    @28
    ctop
    cphtpc
    @15
    cJ
    wceq
    #
    @21
    @27
    vf
    vg
    @30
    @17
    @24
    @20
    @26
    @30
    @17
    @14
    @3
    wss
    @24
    @30
    @16
    @3
    @14
    @15
    cJ
    cii
    ccn
    oveq2
    sseq2d
    @12
    @13
    @3
    vf
    vex
    vg
    vex
    prss
    syl6bbr
    @30
    @19
    @25
    c0
    @30
    @18
    @6
    @12
    @13
    @15
    cJ
    cphtpy
    fveq2
    oveqd
    neeq1d
    anbi12d
    opabbidv
    @23
    @28
    @3
    @3
    cxp
    @3
    @3
    cii
    cJ
    ccn
    ovex
    #
    @31
    xpex
    @26
    vf
    vg
    @3
    @3
    opabssxp
    ssexi
    fvmpt
    breqd
    @29
    @4
    @5
    wa
    @8
    wa
    @9
    @26
    @8
    vf
    vg
    cF
    cG
    @3
    @3
    @28
    @12
    cF
    wceq
    @13
    cG
    wceq
    wa
    @25
    @7
    c0
    @12
    cF
    @13
    cG
    @6
    oveq12
    neeq1d
    @28
    eqid
    brab2a
    @4
    @5
    @8
    df-3an
    bitr4i
    syl6bb
    pm5.21nii
end
