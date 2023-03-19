include "cr.mm"
include "cres.mm"
include "cv.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cxr.mm"
include "cin.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "cinf.mm"
include "clsp.mm"
include "cfv.mm"
include "crn.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "rexrd.mm"
include "ad2antrr.mm"
include "pnfxr.mm"
include "a1i.mm"
include "ressxr.mm"
include "icossre.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "sseldd.mm"
include "simpr.mm"
include "elicore.mm"
include "sseldi.mm"
include "cle.mm"
include "wbr.mm"
include "icogelbd.mm"
include "letrd.mm"
include "ltpnfd.mm"
include "elicod.mm"
include "syl6eleqr.mm"
include "ssd.mm"
include "resima2.mm"
include "syl.mm"
include "ineq1d.mm"
include "supeq1d.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "syl5eqss.mm"
include "mptima2.mm"
include "3eqtr4d.mm"
include "infeq1d.mm"
include "cvv.mm"
include "eqid.mm"
include "resexd.mm"
include "supeq1i.mm"
include "wne.mm"
include "renepnfd.mm"
include "icopnfsup.mm"
include "eqtrd.mm"
include "limsupval2.mm"

theorem limsupresico
  let wph: wff ph
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vk: setvar k
  let vy: setvar y
  assume limsupresico.1: |- ( ph -> M e. RR )
  assume limsupresico.2: |- Z = ( M [,) +oo )
  assume limsupresico.3: |- ( ph -> F e. V )


  assert |- ( ph -> ( limsup ` ( F |` Z ) ) = ( limsup ` F ) )

  proof
    wph
    vk
    cr
    cF
    cZ
    cres
    #
    vk
    cv
    #
    cpnf
    cico
    co
    #
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    cZ
    cima
    #
    cxr
    clt
    cinf
    vk
    cr
    cF
    @2
    cima
    #
    cxr
    cin
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    cZ
    cima
    #
    cxr
    clt
    cinf
    @0
    clsp
    cfv
    cF
    clsp
    cfv
    wph
    cxr
    @7
    @12
    clt
    wph
    vk
    cZ
    @5
    cmpt
    #
    crn
    vk
    cZ
    @10
    cmpt
    #
    crn
    @7
    @12
    wph
    @13
    @14
    wph
    vk
    cZ
    @5
    @10
    wph
    @1
    cZ
    wcel
    #
    wa
    #
    cxr
    @4
    @9
    clt
    @16
    @3
    @8
    cxr
    @16
    @2
    cZ
    wss
    @3
    @8
    wceq
    @16
    vy
    @2
    cZ
    @16
    vy
    cv
    #
    @2
    wcel
    #
    wa
    #
    @17
    cM
    cpnf
    cico
    co
    #
    cZ
    @19
    cM
    cpnf
    @17
    wph
    cM
    cxr
    wcel
    #
    @15
    @18
    wph
    cM
    limsupresico.1
    rexrd
    #
    ad2antrr
    cpnf
    cxr
    wcel
    #
    @19
    pnfxr
    a1i
    #
    @19
    cr
    cxr
    @17
    ressxr
    @19
    @1
    cr
    wcel
    #
    @18
    @17
    cr
    wcel
    @16
    @25
    @18
    @16
    @20
    cr
    @1
    wph
    @20
    cr
    wss
    #
    @15
    wph
    cM
    cr
    wcel
    #
    @23
    @26
    limsupresico.1
    @23
    wph
    pnfxr
    a1i
    cM
    cpnf
    icossre
    syl2anc
    #
    adantr
    @15
    @1
    @20
    wcel
    #
    wph
    @15
    @29
    cZ
    @20
    @1
    limsupresico.2
    eleq2i
    biimpi
    adantl
    #
    sseldd
    adantr
    #
    @16
    @18
    simpr
    #
    @1
    cpnf
    @17
    elicore
    syl2anc
    #
    sseldi
    @19
    cM
    @1
    @17
    wph
    @27
    @15
    @18
    limsupresico.1
    ad2antrr
    @31
    @33
    @16
    cM
    @1
    cle
    wbr
    @18
    @16
    cM
    cpnf
    @1
    wph
    @21
    @15
    @22
    adantr
    @23
    @16
    pnfxr
    a1i
    @30
    icogelbd
    adantr
    @19
    @1
    cpnf
    @17
    @19
    cr
    cxr
    @1
    ressxr
    @31
    sseldi
    @24
    @32
    icogelbd
    letrd
    @19
    @17
    @33
    ltpnfd
    elicod
    limsupresico.2
    syl6eleqr
    ssd
    cF
    @2
    cZ
    resima2
    syl
    ineq1d
    supeq1d
    mpteq2dva
    rneqd
    wph
    vk
    cr
    @5
    cZ
    wph
    cZ
    @20
    cr
    limsupresico.2
    @28
    syl5eqss
    #
    mptima2
    wph
    vk
    cr
    @10
    cZ
    @34
    mptima2
    3eqtr4d
    infeq1d
    wph
    cZ
    vk
    @0
    @6
    cvv
    @6
    eqid
    wph
    cF
    cZ
    cV
    limsupresico.3
    resexd
    @34
    wph
    cZ
    cxr
    clt
    csup
    #
    @20
    cxr
    clt
    csup
    #
    cpnf
    @35
    @36
    wceq
    wph
    cxr
    cZ
    @20
    clt
    limsupresico.2
    supeq1i
    a1i
    wph
    @21
    cM
    cpnf
    wne
    @36
    cpnf
    wceq
    @22
    wph
    cM
    limsupresico.1
    renepnfd
    cM
    icopnfsup
    syl2anc
    eqtrd
    #
    limsupval2
    wph
    cZ
    vk
    cF
    @11
    cV
    @11
    eqid
    limsupresico.3
    @34
    @37
    limsupval2
    3eqtr4d
end
