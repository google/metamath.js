include "c0.mm"
include "csumge0.mm"
include "cfv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cc0.mm"
include "wceq.mm"
include "wtru.mm"
include "cvv.mm"
include "wcel.mm"
include "0ex.mm"
include "a1i.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "f0.mm"
include "wn.mm"
include "noel.mm"
include "rn0.mm"
include "eqcomi.mm"
include "neleqtrd.mm"
include "fge0iccico.mm"
include "sge0reval.mm"
include "trud.mm"
include "csn.mm"
include "wb.mm"
include "wal.mm"
include "wrex.mm"
include "vex.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfv.mm"
include "wi.mm"
include "wa.mm"
include "simpr.mm"
include "elinel1.mm"
include "pw0.mm"
include "eleq2i.mm"
include "syl.mm"
include "elsni.mm"
include "sumeq1d.mm"
include "adantr.mm"
include "sum0.mm"
include "3eqtrd.mm"
include "ex.mm"
include "rexlimd.mm"
include "mpd.mm"
include "velsn.mm"
include "bicomi.mm"
include "0elpw.mm"
include "0fin.mm"
include "pm3.2i.mm"
include "elin.mm"
include "mpbir.mm"
include "sumeq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "cr.mm"
include "0re.mm"
include "eqeltrd.mm"
include "impbii.mm"
include "ax-gen.mm"
include "dfcleq.mm"
include "supeq1i.mm"
include "wor.mm"
include "xrltso.mm"
include "0xr.mm"
include "supsn.mm"
include "eqtri.mm"

theorem sge00
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ( sum^ ` (/) ) = 0

  proof
    c0
    csumge0
    cfv
    #
    vx
    c0
    cpw
    #
    cfn
    cin
    #
    vx
    cv
    #
    vy
    cv
    c0
    cfv
    #
    vy
    csu
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cc0
    @0
    @8
    wceq
    wtru
    vx
    vy
    c0
    cvv
    c0
    c0
    cvv
    wcel
    wtru
    0ex
    a1i
    wtru
    c0
    c0
    c0
    cc0
    cpnf
    cicc
    co
    #
    c0
    wf
    wtru
    @9
    f0
    a1i
    wtru
    c0
    c0
    crn
    #
    cpnf
    cpnf
    c0
    wcel
    wn
    wtru
    cpnf
    noel
    a1i
    c0
    @10
    wceq
    wtru
    @10
    c0
    rn0
    eqcomi
    a1i
    neleqtrd
    fge0iccico
    sge0reval
    trud
    @8
    cc0
    csn
    #
    cxr
    clt
    csup
    #
    cc0
    cxr
    @7
    @11
    clt
    @7
    @11
    wceq
    vz
    cv
    #
    @7
    wcel
    #
    @13
    @11
    wcel
    #
    wb
    #
    vz
    wal
    @16
    vz
    @14
    @15
    @14
    @13
    cc0
    wceq
    #
    @15
    @14
    @13
    @5
    wceq
    #
    vx
    @2
    wrex
    #
    @17
    @14
    @19
    @13
    cvv
    wcel
    @14
    @19
    wb
    vz
    vex
    vx
    @2
    @5
    @13
    @6
    cvv
    @6
    eqid
    #
    elrnmpt
    ax-mp
    biimpi
    @14
    @18
    @17
    vx
    @2
    vx
    @13
    @7
    vx
    @13
    nfcv
    vx
    @6
    vx
    @2
    @5
    nfmpt1
    nfrn
    nfel
    @17
    vx
    nfv
    @3
    @2
    wcel
    #
    @18
    @17
    wi
    wi
    @14
    @21
    @18
    @17
    @21
    @18
    wa
    #
    @13
    @5
    c0
    @4
    vy
    csu
    #
    cc0
    @21
    @18
    simpr
    @21
    @5
    @23
    wceq
    @18
    @21
    @3
    c0
    @4
    vy
    @21
    @3
    c0
    csn
    #
    wcel
    #
    @3
    c0
    wceq
    #
    @21
    @3
    @1
    wcel
    #
    @25
    @3
    @1
    cfn
    elinel1
    @27
    @25
    @1
    @24
    @3
    pw0
    eleq2i
    biimpi
    syl
    @3
    c0
    elsni
    syl
    sumeq1d
    adantr
    @23
    cc0
    wceq
    @22
    @4
    vy
    sum0
    #
    a1i
    3eqtrd
    ex
    a1i
    rexlimd
    mpd
    @17
    @15
    @15
    @17
    vz
    cc0
    velsn
    bicomi
    biimpi
    syl
    @15
    @13
    cc0
    @7
    @13
    cc0
    elsni
    cc0
    @7
    wcel
    #
    @15
    @29
    cc0
    @5
    wceq
    #
    vx
    @2
    wrex
    #
    c0
    @2
    wcel
    #
    cc0
    @23
    wceq
    #
    @31
    @32
    c0
    @1
    wcel
    #
    c0
    cfn
    wcel
    #
    wa
    @34
    @35
    c0
    0elpw
    0fin
    pm3.2i
    c0
    @1
    cfn
    elin
    mpbir
    @23
    cc0
    @28
    eqcomi
    @30
    @33
    vx
    c0
    @2
    @26
    @5
    @23
    cc0
    @3
    c0
    @4
    vy
    sumeq1
    eqeq2d
    rspcev
    mp2an
    cc0
    cr
    wcel
    @29
    @31
    wb
    0re
    vx
    @2
    @5
    cc0
    @6
    cr
    @20
    elrnmpt
    ax-mp
    mpbir
    a1i
    eqeltrd
    impbii
    ax-gen
    vz
    @7
    @11
    dfcleq
    mpbir
    supeq1i
    cxr
    clt
    wor
    cc0
    cxr
    wcel
    @12
    cc0
    wceq
    xrltso
    0xr
    cxr
    cc0
    clt
    supsn
    mp2an
    eqtri
    eqtri
end
