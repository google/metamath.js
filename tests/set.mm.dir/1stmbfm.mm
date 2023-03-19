include "c1st.mm"
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
include "f1stres.mm"
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
include "xpss1.mm"
include "sseld.mm"
include "pm4.71rd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "fvres.mm"
include "eleq1d.mm"
include "c2nd.mm"
include "cop.mm"
include "1st2nd2.mm"
include "xp2nd.mm"
include "elxp6.mm"
include "anass.mm"
include "an32.mm"
include "3bitr2i.mm"
include "baib.mm"
include "bitr4d.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "syl6rbbr.mm"
include "eqrdv.mm"
include "adantr.mm"
include "simpr.mm"
include "eqid.mm"
include "issgon.mm"
include "sylanblrc.mm"
include "baselsiga.mm"
include "elsx.mm"
include "syl22anc.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ismbfm.mm"
include "mpbir2and.mm"

theorem 1stmbfm
  let wph: wff ph
  let cS: class S
  let cT: class T
  let va: setvar a
  let vz: setvar z
  assume 1stmbfm.1: |- ( ph -> S e. U. ran sigAlgebra )
  assume 1stmbfm.2: |- ( ph -> T e. U. ran sigAlgebra )


  assert |- ( ph -> ( 1st |` ( U. S X. U. T ) ) e. ( ( S sX T ) MblFnM S ) )

  proof
    wph
    c1st
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
    cS
    cmbfm
    co
    wcel
    @3
    @0
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
    cS
    wral
    wph
    @6
    @5
    @0
    @3
    wf
    #
    wph
    @2
    @0
    @3
    wf
    #
    @10
    @0
    @1
    f1stres
    #
    wph
    @2
    @5
    @0
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
    @0
    @5
    @3
    cS
    @4
    wph
    @14
    @0
    cS
    wcel
    1stmbfm.1
    cS
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
    cS
    wph
    @7
    cS
    wcel
    #
    wa
    #
    @8
    @7
    @1
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
    @0
    wss
    #
    @20
    @2
    wss
    wph
    @26
    va
    cS
    wph
    @14
    cS
    @0
    csiga
    cfv
    wcel
    cS
    @0
    cpw
    wss
    #
    @26
    va
    cS
    wral
    #
    1stmbfm.1
    cS
    sgon
    @0
    cS
    sigasspw
    @27
    @28
    va
    cS
    @0
    pwssb
    biimpi
    4syl
    r19.21bi
    @7
    @0
    @1
    xpss1
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
    @0
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
    c1st
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
    c1st
    fvres
    eleq1d
    @23
    @21
    @32
    @21
    c2nd
    cfv
    #
    cop
    wceq
    #
    @34
    @1
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
    xp2nd
    @22
    @35
    @36
    wa
    #
    @33
    @22
    @35
    @33
    @36
    wa
    wa
    @35
    @33
    wa
    @36
    wa
    @37
    @33
    wa
    @21
    @7
    @1
    elxp6
    @35
    @33
    @36
    anass
    @35
    @33
    @36
    an32
    3bitr2i
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
    @18
    @1
    cT
    wcel
    #
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
    @18
    simpr
    wph
    @38
    @18
    wph
    cT
    @1
    csiga
    cfv
    wcel
    #
    @38
    wph
    @15
    @1
    @1
    wceq
    @39
    1stmbfm.2
    @1
    eqid
    cT
    @1
    issgon
    sylanblrc
    @1
    cT
    baselsiga
    syl
    adantr
    @7
    @1
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
    cS
    @3
    @17
    1stmbfm.1
    ismbfm
    mpbir2and
end
