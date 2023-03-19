include "crn.mm"
include "cpjh.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "chil.mm"
include "wfn.mm"
include "wral.mm"
include "wb.mm"
include "wf.mm"
include "cho.mm"
include "wcel.mm"
include "clo.mm"
include "hmoplin.mm"
include "ax-mp.mm"
include "lnopfi.mm"
include "ffn.mm"
include "hmopidmchi.mm"
include "pjfni.mm"
include "eqfnfv.mm"
include "mp2an.mm"
include "cmv.mm"
include "co.mm"
include "cva.mm"
include "cort.mm"
include "fnfvelrn.mm"
include "mpan.mm"
include "csp.mm"
include "cc0.mm"
include "id.mm"
include "ffvelrni.mm"
include "hvsubcl.mm"
include "syl2anc.mm"
include "wa.mm"
include "cmin.mm"
include "simpl.mm"
include "adantr.mm"
include "adantl.mm"
include "his2sub.mm"
include "syl3anc.mm"
include "hmop.mm"
include "mp3an1.mm"
include "sylan2.mm"
include "ccom.mm"
include "fveq1i.mm"
include "hocoi.mm"
include "syl5reqr.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "cc.mm"
include "hicl.mm"
include "subidd.mm"
include "3eqtrd.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "ralrn.mm"
include "sylibr.mm"
include "wss.mm"
include "chssii.mm"
include "ocel.mm"
include "sylanbrc.mm"
include "pjcompi.mm"
include "hvpncan3.mm"
include "fveq2d.mm"
include "mprgbir.mm"

theorem hmopidmpji
  let cT: class T
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume hmopidmch.1: |- T e. HrmOp
  assume hmopidmch.2: |- ( T o. T ) = T


  assert |- T = ( projh ` ran T )

  proof
    cT
    cT
    crn
    #
    cpjh
    cfv
    #
    wceq
    #
    vx
    cv
    #
    cT
    cfv
    #
    @3
    @1
    cfv
    #
    wceq
    #
    vx
    chil
    cT
    chil
    wfn
    #
    @1
    chil
    wfn
    @2
    @6
    vx
    chil
    wral
    wb
    chil
    chil
    cT
    wf
    @7
    cT
    cT
    cho
    wcel
    #
    cT
    clo
    wcel
    hmopidmch.1
    cT
    hmoplin
    ax-mp
    lnopfi
    #
    chil
    chil
    cT
    ffn
    ax-mp
    #
    @0
    cT
    hmopidmch.1
    hmopidmch.2
    hmopidmchi
    #
    pjfni
    vx
    chil
    cT
    @1
    eqfnfv
    mp2an
    @3
    chil
    wcel
    #
    @4
    @3
    @4
    cmv
    co
    #
    cva
    co
    #
    @1
    cfv
    #
    @4
    @5
    @12
    @4
    @0
    wcel
    #
    @13
    @0
    cort
    cfv
    wcel
    #
    @15
    @4
    wceq
    @7
    @12
    @16
    @10
    chil
    @3
    cT
    fnfvelrn
    mpan
    @12
    @13
    chil
    wcel
    #
    @13
    vz
    cv
    #
    csp
    co
    #
    cc0
    wceq
    #
    vz
    @0
    wral
    #
    @17
    @12
    @12
    @4
    chil
    wcel
    #
    @18
    @12
    id
    #
    chil
    chil
    @3
    cT
    @9
    ffvelrni
    #
    @3
    @4
    hvsubcl
    syl2anc
    @12
    @13
    vy
    cv
    #
    cT
    cfv
    #
    csp
    co
    #
    cc0
    wceq
    #
    vy
    chil
    wral
    #
    @22
    @12
    @29
    vy
    chil
    @12
    @26
    chil
    wcel
    #
    wa
    #
    @28
    @3
    @27
    csp
    co
    #
    @4
    @27
    csp
    co
    #
    cmin
    co
    #
    @33
    @33
    cmin
    co
    cc0
    @32
    @12
    @23
    @27
    chil
    wcel
    #
    @28
    @35
    wceq
    @12
    @31
    simpl
    @12
    @23
    @31
    @25
    adantr
    @31
    @36
    @12
    chil
    chil
    @26
    cT
    @9
    ffvelrni
    #
    adantl
    @3
    @4
    @27
    his2sub
    syl3anc
    @32
    @34
    @33
    @33
    cmin
    @32
    @3
    @27
    cT
    cfv
    #
    csp
    co
    #
    @34
    @33
    @31
    @12
    @36
    @39
    @34
    wceq
    #
    @37
    @8
    @12
    @36
    @40
    hmopidmch.1
    @3
    @27
    cT
    hmop
    mp3an1
    sylan2
    @32
    @38
    @27
    @3
    csp
    @31
    @38
    @27
    wceq
    @12
    @31
    @27
    @26
    cT
    cT
    ccom
    #
    cfv
    @38
    @26
    @41
    cT
    hmopidmch.2
    fveq1i
    @26
    cT
    cT
    @9
    @9
    hocoi
    syl5reqr
    adantl
    oveq2d
    eqtr3d
    oveq2d
    @32
    @33
    @31
    @12
    @36
    @33
    cc
    wcel
    @37
    @3
    @27
    hicl
    sylan2
    subidd
    3eqtrd
    ralrimiva
    @7
    @22
    @30
    wb
    @10
    @21
    @29
    vz
    vy
    chil
    cT
    @19
    @27
    wceq
    @20
    @28
    cc0
    @19
    @27
    @13
    csp
    oveq2
    eqeq1d
    ralrn
    ax-mp
    sylibr
    @0
    chil
    wss
    @17
    @18
    @22
    wa
    wb
    @0
    @11
    chssii
    vz
    @13
    @0
    ocel
    ax-mp
    sylanbrc
    @4
    @13
    @0
    @11
    pjcompi
    syl2anc
    @12
    @14
    @3
    @1
    @12
    @23
    @12
    @14
    @3
    wceq
    @25
    @24
    @4
    @3
    hvpncan3
    syl2anc
    fveq2d
    eqtr3d
    mprgbir
end
