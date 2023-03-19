include "cv.mm"
include "wcel.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "wb.mm"
include "wal.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "wf.mm"
include "sselda.mm"
include "elmapi.mm"
include "syl.mm"
include "ffnd.mm"
include "crn.mm"
include "ciun.mm"
include "a1i.mm"
include "wral.mm"
include "ovexd.mm"
include "ssexd.mm"
include "rnexg.mm"
include "rgen.mm"
include "jca.mm"
include "iunexg.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "cfv.mm"
include "wss.mm"
include "ssiun2.mm"
include "adantl.mm"
include "wfn.mm"
include "snidg.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "syl6eleqr.mm"
include "elmapsnd.mm"
include "ex.mm"
include "wrex.mm"
include "snex.mm"
include "simpr.mm"
include "fvmap.mm"
include "idi.mm"
include "rneq.mm"
include "cbviunv.mm"
include "eqtri.mm"
include "syl6eleq.mm"
include "eliun.mm"
include "sylib.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1l.mm"
include "eqid.mm"
include "simp1r.mm"
include "elmapfn.mm"
include "3adant3.mm"
include "3adant1r.mm"
include "fsneqrn.mm"
include "mpbird.mm"
include "simp2.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "impbid.mm"
include "alrimiv.mm"
include "nfcv.mm"
include "nfov.mm"
include "dfcleqf.mm"
include "sylibr.mm"

theorem ssmapsn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let cV: class V
  let vg: setvar g
  assume ssmapsn.f: |- F/_ f D
  assume ssmapsn.a: |- ( ph -> A e. V )
  assume ssmapsn.c: |- ( ph -> C C_ ( B ^m { A } ) )
  assume ssmapsn.d: |- D = U_ f e. C ran f

  disjoint A f
  disjoint C f
  disjoint f ph
  disjoint A g
  disjoint f g
  disjoint C g
  disjoint D g
  disjoint g ph
  assert |- ( ph -> C = ( D ^m { A } ) )

  proof
    wph
    vf
    cv
    #
    cC
    wcel
    #
    @0
    cD
    cA
    csn
    #
    cmap
    co
    #
    wcel
    #
    wb
    #
    vf
    wal
    cC
    @3
    wceq
    wph
    @5
    vf
    wph
    @1
    @4
    wph
    @1
    @4
    wph
    @1
    wa
    #
    cA
    cD
    @0
    cvv
    @6
    @2
    cB
    @0
    @6
    @0
    cB
    @2
    cmap
    co
    #
    wcel
    @2
    cB
    @0
    wf
    wph
    cC
    @7
    @0
    ssmapsn.c
    sselda
    @0
    cB
    @2
    elmapi
    syl
    ffnd
    #
    wph
    cD
    cvv
    wcel
    #
    @1
    wph
    cD
    vf
    cC
    @0
    crn
    #
    ciun
    #
    cvv
    cD
    @11
    wceq
    #
    wph
    ssmapsn.d
    a1i
    wph
    cC
    cvv
    wcel
    #
    @10
    cvv
    wcel
    #
    vf
    cC
    wral
    #
    wa
    @11
    cvv
    wcel
    wph
    @13
    @15
    wph
    cC
    @7
    cvv
    wph
    cB
    @2
    cmap
    ovexd
    ssmapsn.c
    ssexd
    @15
    wph
    @14
    vf
    cC
    @0
    cC
    rnexg
    rgen
    a1i
    jca
    vf
    cC
    @10
    cvv
    cvv
    iunexg
    syl
    eqeltrd
    #
    adantr
    @6
    cA
    @0
    cfv
    #
    @11
    cD
    @6
    @10
    @11
    @17
    @1
    @10
    @11
    wss
    wph
    vf
    cC
    @10
    ssiun2
    adantl
    @6
    @0
    @2
    wfn
    #
    cA
    @2
    wcel
    #
    @17
    @10
    wcel
    @8
    wph
    @19
    @1
    wph
    cA
    cV
    wcel
    #
    @19
    ssmapsn.a
    cA
    cV
    snidg
    syl
    #
    adantr
    @2
    cA
    @0
    fnfvelrn
    syl2anc
    sseldd
    ssmapsn.d
    syl6eleqr
    elmapsnd
    ex
    wph
    @4
    @1
    wph
    @4
    wa
    #
    @17
    vg
    cv
    #
    crn
    #
    wcel
    #
    vg
    cC
    wrex
    #
    @1
    @22
    @17
    vg
    cC
    @24
    ciun
    #
    wcel
    @26
    @22
    @17
    cD
    @27
    @22
    cD
    @2
    cA
    @0
    cvv
    cvv
    wph
    @9
    @4
    @16
    adantr
    @2
    cvv
    wcel
    @22
    cA
    snex
    a1i
    wph
    @4
    simpr
    wph
    @19
    @4
    @21
    adantr
    fvmap
    cD
    @11
    @27
    @12
    ssmapsn.d
    idi
    vf
    vg
    cC
    @10
    @24
    @0
    @23
    rneq
    cbviunv
    eqtri
    syl6eleq
    vg
    @17
    cC
    @24
    eliun
    sylib
    @22
    @25
    @1
    vg
    cC
    @22
    @23
    cC
    wcel
    #
    @25
    @1
    @22
    @28
    @25
    w3a
    #
    @0
    @23
    cC
    @29
    @0
    @23
    wceq
    @25
    @22
    @28
    @25
    simp3
    @29
    cA
    @2
    @0
    @23
    cV
    @29
    wph
    @20
    wph
    @4
    @28
    @25
    simp1l
    ssmapsn.a
    syl
    @2
    eqid
    @29
    @4
    @18
    wph
    @4
    @28
    @25
    simp1r
    @0
    cD
    @2
    elmapfn
    syl
    wph
    @28
    @25
    @23
    @2
    wfn
    #
    @4
    wph
    @28
    @30
    @25
    wph
    @28
    wa
    @23
    @7
    wcel
    @30
    wph
    cC
    @7
    @23
    ssmapsn.c
    sselda
    @23
    cB
    @2
    elmapfn
    syl
    3adant3
    3adant1r
    fsneqrn
    mpbird
    @22
    @28
    @25
    simp2
    eqeltrd
    3exp
    rexlimdv
    mpd
    ex
    impbid
    alrimiv
    vf
    cC
    @3
    vf
    cC
    nfcv
    vf
    cD
    @2
    cmap
    ssmapsn.f
    vf
    cmap
    nfcv
    vf
    @2
    nfcv
    nfov
    dfcleqf
    sylibr
end
