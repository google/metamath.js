include "c2nd.mm"
include "cuni.mm"
include "cxp.mm"
include "cres.mm"
include "csx.mm"
include "co.mm"
include "cmbfm.mm"
include "wcel.mm"
include "cmap.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "wf.mm"
include "f2ndres.mm"
include "csiga.mm"
include "crn.mm"
include "wceq.mm"
include "sxuni.mm"
include "syl2anc.mm"
include "feq2d.mm"
include "mpbii.mm"
include "unielsiga.mm"
include "syl.mm"
include "sxsiga.mm"
include "elmapd.mm"
include "mpbird.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cpw.mm"
include "sgon.mm"
include "sigasspw.mm"
include "pwssb.mm"
include "biimpi.mm"
include "4syl.mm"
include "r19.21bi.mm"
include "xpss2.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "fvres.mm"
include "eleq1d.mm"
include "c1st.mm"
include "cop.mm"
include "1st2nd2.mm"
include "xp1st.mm"
include "elxp6.mm"
include "anass.mm"
include "bitr4i.mm"
include "baib.mm"
include "bitr4d.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "eqrdv.mm"
include "adantr.mm"
include "eqid.mm"
include "issgon.mm"
include "sylanblrc.mm"
include "baselsiga.mm"
include "simpr.mm"
include "elsx.mm"
include "syl22anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ismbfm.mm"
include "mpbir2and.mm"

theorem 2ndmbfm
  let wph: wff ph
  let cS: class S
  let cT: class T
  let va: setvar a
  let vz: setvar z
  assume 1stmbfm.1: |- ( ph -> S e. U. ran sigAlgebra )
  assume 1stmbfm.2: |- ( ph -> T e. U. ran sigAlgebra )


  assert |- ( ph -> ( 2nd |` ( U. S X. U. T ) ) e. ( ( S sX T ) MblFnM T ) )

  proof
    wph
    c2nd
    cS
    cuni
    #
    cT
    cuni
    #
    cxp
    #
    cres
    #
    cS
    cT
    csx
    co
    #
    cT
    cmbfm
    co
    wcel
    @3
    @1
    @4
    cuni
    #
    cmap
    co
    wcel
    #
    @3
    ccnv
    va
    cv
    #
    cima
    #
    @4
    wcel
    #
    va
    cT
    wral
    wph
    @6
    @5
    @1
    @3
    wf
    #
    wph
    @2
    @1
    @3
    wf
    #
    @10
    @0
    @1
    f2ndres
    #
    wph
    @2
    @5
    @1
    @3
    wph
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    cT
    @13
    wcel
    #
    @2
    @5
    wceq
    1stmbfm.1
    1stmbfm.2
    cS
    cT
    sxuni
    syl2anc
    feq2d
    mpbii
    wph
    @1
    @5
    @3
    cT
    @4
    wph
    @15
    @1
    cT
    wcel
    1stmbfm.2
    cT
    unielsiga
    syl
    wph
    @4
    @13
    wcel
    #
    @5
    @4
    wcel
    wph
    @14
    @15
    @16
    1stmbfm.1
    1stmbfm.2
    cS
    cT
    sxsiga
    syl2anc
    #
    @4
    unielsiga
    syl
    elmapd
    mpbird
    wph
    @9
    va
    cT
    wph
    @7
    cT
    wcel
    #
    wa
    #
    @8
    @0
    @7
    cxp
    #
    @4
    @19
    vz
    @8
    @20
    @19
    vz
    cv
    #
    @20
    wcel
    #
    @21
    @2
    wcel
    #
    @22
    wa
    #
    @21
    @8
    wcel
    #
    @19
    @22
    @23
    @19
    @20
    @2
    @21
    @19
    @7
    @1
    wss
    #
    @20
    @2
    wss
    wph
    @26
    va
    cT
    wph
    @15
    cT
    @1
    csiga
    cfv
    wcel
    cT
    @1
    cpw
    wss
    #
    @26
    va
    cT
    wral
    #
    1stmbfm.2
    cT
    sgon
    @1
    cT
    sigasspw
    @27
    @28
    va
    cT
    @1
    pwssb
    biimpi
    4syl
    r19.21bi
    @7
    @1
    @0
    xpss2
    syl
    sseld
    pm4.71rd
    @25
    @23
    @21
    @3
    cfv
    #
    @7
    wcel
    #
    wa
    #
    @24
    @11
    @3
    @2
    wfn
    @25
    @31
    wb
    @12
    @2
    @1
    @3
    ffn
    @2
    @21
    @7
    @3
    elpreima
    mp2b
    @23
    @30
    @22
    @23
    @30
    @21
    c2nd
    cfv
    #
    @7
    wcel
    #
    @22
    @23
    @29
    @32
    @7
    @21
    @2
    c2nd
    fvres
    eleq1d
    @23
    @21
    @21
    c1st
    cfv
    #
    @32
    cop
    wceq
    #
    @34
    @0
    wcel
    #
    @22
    @33
    wb
    @21
    @0
    @1
    1st2nd2
    @21
    @0
    @1
    xp1st
    @22
    @35
    @36
    wa
    #
    @33
    @22
    @35
    @36
    @33
    wa
    wa
    @37
    @33
    wa
    @21
    @0
    @7
    elxp6
    @35
    @36
    @33
    anass
    bitr4i
    baib
    syl2anc
    bitr4d
    pm5.32i
    bitri
    syl6rbbr
    eqrdv
    @19
    @14
    @15
    @0
    cS
    wcel
    #
    @18
    @20
    @4
    wcel
    wph
    @14
    @18
    1stmbfm.1
    adantr
    wph
    @15
    @18
    1stmbfm.2
    adantr
    wph
    @38
    @18
    wph
    cS
    @0
    csiga
    cfv
    wcel
    #
    @38
    wph
    @14
    @0
    @0
    wceq
    @39
    1stmbfm.1
    @0
    eqid
    cS
    @0
    issgon
    sylanblrc
    @0
    cS
    baselsiga
    syl
    adantr
    wph
    @18
    simpr
    @0
    @7
    cS
    cT
    @13
    @13
    elsx
    syl22anc
    eqeltrd
    ralrimiva
    wph
    va
    @4
    cT
    @3
    @17
    1stmbfm.2
    ismbfm
    mpbir2and
end
