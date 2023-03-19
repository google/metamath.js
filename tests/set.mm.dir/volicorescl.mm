include "cico.mm"
include "cr.mm"
include "cxp.mm"
include "cres.mm"
include "crn.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cvol.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cxr.mm"
include "crab.mm"
include "cmpt2.mm"
include "df-ico.mm"
include "reseq1i.mm"
include "wss.mm"
include "ressxr.mm"
include "resmpt2.mm"
include "mp2an.mm"
include "eqtri.mm"
include "rneqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "eqid.mm"
include "xrex.mm"
include "rabex.mm"
include "elrnmpt2.mm"
include "sylib.mm"
include "wi.mm"
include "simpr.mm"
include "sseli.mm"
include "adantr.mm"
include "adantl.mm"
include "icoval.mm"
include "syl2anc.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "ex.mm"
include "adantll.mm"
include "reximdva.mm"
include "mpd.mm"
include "fveq2.mm"
include "volicorecl.mm"
include "eqeltrd.mm"
include "a1i.mm"
include "rexlimdvv.mm"
include "2a1d.mm"

theorem volicorescl
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k


  assert |- ( A e. ran ( [,) |` ( RR X. RR ) ) -> ( vol ` A ) e. RR )

  proof
    cA
    cico
    cr
    cr
    cxp
    #
    cres
    #
    crn
    #
    wcel
    #
    cA
    vx
    cv
    #
    vy
    cv
    #
    cico
    co
    #
    wceq
    #
    vy
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    cA
    cvol
    cfv
    #
    cr
    wcel
    #
    @3
    cA
    @4
    vz
    cv
    #
    cle
    wbr
    @12
    @5
    clt
    wbr
    wa
    #
    vz
    cxr
    crab
    #
    wceq
    #
    vy
    cr
    wrex
    #
    vx
    cr
    wrex
    #
    @9
    @3
    cA
    vx
    vy
    cr
    cr
    @14
    cmpt2
    #
    crn
    #
    wcel
    #
    @17
    @3
    @20
    @2
    @19
    cA
    @1
    @18
    @1
    vx
    vy
    cxr
    cxr
    @14
    cmpt2
    #
    @0
    cres
    #
    @18
    cico
    @21
    @0
    vx
    vy
    vz
    df-ico
    reseq1i
    cr
    cxr
    wss
    #
    @23
    @22
    @18
    wceq
    ressxr
    ressxr
    vx
    vy
    cxr
    cxr
    cr
    cr
    @14
    resmpt2
    mp2an
    eqtri
    rneqi
    eleq2i
    biimpi
    vx
    vy
    cr
    cr
    @14
    cA
    @18
    @18
    eqid
    @13
    vz
    cxr
    xrex
    rabex
    elrnmpt2
    sylib
    @3
    @16
    @8
    vx
    cr
    @3
    @4
    cr
    wcel
    #
    wa
    @15
    @7
    vy
    cr
    @24
    @5
    cr
    wcel
    #
    @15
    @7
    wi
    @3
    @24
    @25
    wa
    #
    @15
    @7
    @26
    @15
    wa
    cA
    @14
    @6
    @26
    @15
    simpr
    @26
    @14
    @6
    wceq
    @15
    @26
    @6
    @14
    @26
    @4
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @6
    @14
    wceq
    @24
    @27
    @25
    cr
    cxr
    @4
    ressxr
    sseli
    adantr
    @25
    @28
    @24
    cr
    cxr
    @5
    ressxr
    sseli
    adantl
    vz
    @4
    @5
    icoval
    syl2anc
    eqcomd
    adantr
    eqtrd
    ex
    adantll
    reximdva
    reximdva
    mpd
    #
    @3
    @7
    @11
    vx
    vy
    cr
    cr
    @3
    @11
    @26
    @7
    @3
    @9
    @11
    @29
    @3
    @7
    @11
    vx
    vy
    cr
    cr
    @26
    @7
    @11
    wi
    wi
    @3
    @26
    @7
    @11
    @26
    @7
    wa
    @10
    @6
    cvol
    cfv
    #
    cr
    @7
    @10
    @30
    wceq
    @26
    cA
    @6
    cvol
    fveq2
    adantl
    @26
    @30
    cr
    wcel
    @7
    @4
    @5
    volicorecl
    adantr
    eqeltrd
    ex
    a1i
    rexlimdvv
    mpd
    2a1d
    rexlimdvv
    mpd
end
