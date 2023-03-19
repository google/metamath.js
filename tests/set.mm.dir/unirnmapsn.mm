include "cuni.mm"
include "crn.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "snex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "unirnmap.mm"
include "cv.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cfv.mm"
include "wrex.mm"
include "ciun.mm"
include "simpl.mm"
include "equid.mm"
include "rnuni.mm"
include "oveq1i.mm"
include "eleq12i.mm"
include "biimpi.mm"
include "adantl.mm"
include "wf.mm"
include "ovexd.mm"
include "ssexd.mm"
include "rnexg.mm"
include "rgen.mm"
include "iunexg.mm"
include "syl2anc.mm"
include "elmapd.mm"
include "biimpa.mm"
include "snidg.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "eliun.mm"
include "sylib.mm"
include "wfn.mm"
include "wi.mm"
include "elmapfn.mm"
include "w3a.mm"
include "wceq.mm"
include "simp3.mm"
include "3ad2ant1.mm"
include "oveq2i.mm"
include "syl6sseq.mm"
include "simpr.mm"
include "sseldd.mm"
include "mpbid.mm"
include "3adant3.mm"
include "rnsnf.mm"
include "eleqtrd.mm"
include "fvex.mm"
include "elsn.mm"
include "3adant1r.mm"
include "simp1r.mm"
include "adantlr.mm"
include "fsneq.mm"
include "mpbird.mm"
include "simp2.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "eqssd.mm"

theorem unirnmapsn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  assume unirnmapsn.A: |- ( ph -> A e. V )
  assume unirnmapsn.b: |- ( ph -> B e. W )
  assume unirnmapsn.C: |- C = { A }
  assume unirnmapsn.x: |- ( ph -> X C_ ( B ^m C ) )


  assert |- ( ph -> X = ( ran U. X ^m C ) )

  proof
    wph
    cX
    cX
    cuni
    crn
    #
    cC
    cmap
    co
    #
    wph
    cC
    cB
    cvv
    cX
    cC
    cvv
    wcel
    wph
    cC
    cA
    csn
    #
    cvv
    unirnmapsn.C
    cA
    snex
    #
    eqeltri
    a1i
    #
    unirnmapsn.x
    unirnmap
    wph
    vg
    cv
    #
    cX
    wcel
    #
    vg
    @1
    wral
    @1
    cX
    wss
    wph
    @6
    vg
    @1
    wph
    @5
    @1
    wcel
    #
    wa
    #
    cA
    @5
    cfv
    #
    vf
    cv
    #
    crn
    #
    wcel
    #
    vf
    cX
    wrex
    #
    @6
    @8
    wph
    @5
    vf
    cX
    @11
    ciun
    #
    cC
    cmap
    co
    #
    wcel
    #
    @13
    wph
    @7
    simpl
    #
    @7
    @16
    wph
    @7
    @16
    @5
    @5
    @1
    @15
    vg
    equid
    @0
    @14
    cC
    cmap
    vf
    cX
    rnuni
    oveq1i
    eleq12i
    biimpi
    adantl
    wph
    @16
    wa
    #
    @9
    @14
    wcel
    @13
    @18
    cC
    @14
    cA
    @5
    wph
    @16
    cC
    @14
    @5
    wf
    wph
    @14
    cC
    @5
    cvv
    cvv
    wph
    cX
    cvv
    wcel
    @11
    cvv
    wcel
    #
    vf
    cX
    wral
    #
    @14
    cvv
    wcel
    wph
    cX
    cB
    cC
    cmap
    co
    #
    cvv
    wph
    cB
    cC
    cmap
    ovexd
    unirnmapsn.x
    ssexd
    @20
    wph
    @19
    vf
    cX
    @10
    cX
    rnexg
    rgen
    a1i
    vf
    cX
    @11
    cvv
    cvv
    iunexg
    syl2anc
    @4
    elmapd
    biimpa
    wph
    cA
    cC
    wcel
    @16
    wph
    cA
    @2
    cC
    wph
    cA
    cV
    wcel
    #
    cA
    @2
    wcel
    unirnmapsn.A
    cA
    cV
    snidg
    syl
    unirnmapsn.C
    syl6eleqr
    adantr
    ffvelrnd
    vf
    @9
    cX
    @11
    eliun
    sylib
    syl2anc
    @8
    @12
    @6
    vf
    cX
    @8
    wph
    @5
    cC
    wfn
    #
    @10
    cX
    wcel
    #
    @12
    @6
    wi
    wi
    @17
    @7
    @23
    wph
    @5
    @0
    cC
    elmapfn
    adantl
    wph
    @23
    wa
    #
    @24
    @12
    @6
    @25
    @24
    @12
    w3a
    #
    @5
    @10
    cX
    @26
    @5
    @10
    wceq
    @9
    cA
    @10
    cfv
    #
    wceq
    #
    wph
    @24
    @12
    @28
    @23
    wph
    @24
    @12
    w3a
    #
    @9
    @27
    csn
    #
    wcel
    @28
    @29
    @9
    @11
    @30
    wph
    @24
    @12
    simp3
    @29
    cA
    cB
    @10
    cV
    wph
    @24
    @22
    @12
    unirnmapsn.A
    3ad2ant1
    wph
    @24
    @2
    cB
    @10
    wf
    #
    @12
    wph
    @24
    wa
    #
    @10
    cB
    @2
    cmap
    co
    #
    wcel
    @31
    @32
    cX
    @33
    @10
    wph
    cX
    @33
    wss
    @24
    wph
    cX
    @21
    @33
    unirnmapsn.x
    cC
    @2
    cB
    cmap
    unirnmapsn.C
    oveq2i
    #
    syl6sseq
    adantr
    wph
    @24
    simpr
    sseldd
    #
    @32
    cB
    @2
    @10
    cW
    cvv
    wph
    cB
    cW
    wcel
    @24
    unirnmapsn.b
    adantr
    @2
    cvv
    wcel
    @32
    @3
    a1i
    elmapd
    mpbid
    3adant3
    rnsnf
    eleqtrd
    @9
    @27
    cA
    @5
    fvex
    elsn
    sylib
    3adant1r
    @26
    cA
    cC
    @5
    @10
    cV
    @25
    @24
    @22
    @12
    wph
    @22
    @23
    unirnmapsn.A
    adantr
    3ad2ant1
    unirnmapsn.C
    wph
    @23
    @24
    @12
    simp1r
    @25
    @24
    @10
    cC
    wfn
    #
    @12
    wph
    @24
    @36
    @23
    @32
    @10
    @21
    wcel
    @36
    @32
    @10
    @33
    @21
    @35
    @34
    syl6eleqr
    @10
    cB
    cC
    elmapfn
    syl
    adantlr
    3adant3
    fsneq
    mpbird
    @25
    @24
    @12
    simp2
    eqeltrd
    3exp
    syl2anc
    rexlimdv
    mpd
    ralrimiva
    vg
    @1
    cX
    dfss3
    sylibr
    eqssd
end
