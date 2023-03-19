include "cfv.mm"
include "cdif.mm"
include "cxad.mm"
include "co.mm"
include "cle.mm"
include "cc0.mm"
include "wbr.mm"
include "cpnf.mm"
include "cicc.mm"
include "wcel.mm"
include "cmeas.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "measbase.mm"
include "syl.mm"
include "difelsiga.mm"
include "syl3anc.mm"
include "measvxrge0.mm"
include "syl2anc.mm"
include "cxr.mm"
include "elxrge0.mm"
include "simprbi.mm"
include "wi.mm"
include "simplbi.mm"
include "xraddge02.mm"
include "mpd.mm"
include "cpr.mm"
include "cv.mm"
include "cesum.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wdisj.mm"
include "wceq.mm"
include "wss.mm"
include "prssi.mm"
include "prex.mm"
include "elpw.mm"
include "sylibr.mm"
include "prct.mm"
include "disjdifprg.mm"
include "prcom.mm"
include "a1i.mm"
include "disjeq1d.mm"
include "mpbid.mm"
include "measvun.mm"
include "syl112anc.mm"
include "cun.mm"
include "uniprg.mm"
include "undif.mm"
include "sylib.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "adantl.mm"
include "wo.mm"
include "wa.mm"
include "c0.mm"
include "eqimss.mm"
include "ssdifeq0.mm"
include "measvnul.mm"
include "adantr.mm"
include "orcd.mm"
include "ex.mm"
include "esumpr2.mm"
include "3eqtr3d.mm"
include "breqtrrd.mm"

theorem measssd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cM: class M
  let vy: setvar y
  assume measssd.1: |- ( ph -> M e. ( measures ` S ) )
  assume measssd.2: |- ( ph -> A e. S )
  assume measssd.3: |- ( ph -> B e. S )
  assume measssd.4: |- ( ph -> A C_ B )


  assert |- ( ph -> ( M ` A ) <_ ( M ` B ) )

  proof
    wph
    cA
    cM
    cfv
    #
    @0
    cB
    cA
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    cB
    cM
    cfv
    #
    cle
    wph
    cc0
    @2
    cle
    wbr
    #
    @0
    @3
    cle
    wbr
    #
    wph
    @2
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @5
    wph
    cM
    cS
    cmeas
    cfv
    wcel
    #
    @1
    cS
    wcel
    #
    @8
    measssd.1
    wph
    cS
    csiga
    crn
    cuni
    wcel
    #
    cB
    cS
    wcel
    #
    cA
    cS
    wcel
    #
    @10
    wph
    @9
    @11
    measssd.1
    cS
    cM
    measbase
    syl
    measssd.3
    measssd.2
    cB
    cA
    cS
    difelsiga
    syl3anc
    #
    @1
    cS
    cM
    measvxrge0
    syl2anc
    #
    @8
    @2
    cxr
    wcel
    #
    @5
    @2
    elxrge0
    #
    simprbi
    syl
    wph
    @0
    cxr
    wcel
    #
    @16
    @5
    @6
    wi
    wph
    @0
    @7
    wcel
    #
    @18
    wph
    @9
    @13
    @19
    measssd.1
    measssd.2
    cA
    cS
    cM
    measvxrge0
    syl2anc
    #
    @19
    @18
    cc0
    @0
    cle
    wbr
    @0
    elxrge0
    simplbi
    syl
    wph
    @8
    @16
    @15
    @8
    @16
    @5
    @17
    simplbi
    syl
    @0
    @2
    xraddge02
    syl2anc
    mpd
    wph
    cA
    @1
    cpr
    #
    cuni
    #
    cM
    cfv
    #
    @21
    vy
    cv
    #
    cM
    cfv
    #
    vy
    cesum
    #
    @4
    @3
    wph
    @9
    @21
    cS
    cpw
    wcel
    #
    @21
    com
    cdom
    wbr
    #
    vy
    @21
    @24
    wdisj
    #
    @23
    @26
    wceq
    measssd.1
    wph
    @21
    cS
    wss
    #
    @27
    wph
    @13
    @10
    @30
    measssd.2
    @14
    cA
    @1
    cS
    prssi
    syl2anc
    @21
    cS
    cA
    @1
    prex
    elpw
    sylibr
    wph
    @13
    @10
    @28
    measssd.2
    @14
    cA
    @1
    cS
    cS
    prct
    syl2anc
    wph
    vy
    @1
    cA
    cpr
    #
    @24
    wdisj
    #
    @29
    wph
    @13
    @12
    @32
    measssd.2
    measssd.3
    vy
    cA
    cB
    cS
    cS
    disjdifprg
    syl2anc
    wph
    vy
    @31
    @21
    @24
    @31
    @21
    wceq
    wph
    @1
    cA
    prcom
    a1i
    disjeq1d
    mpbid
    vy
    @21
    cS
    cM
    measvun
    syl112anc
    wph
    @22
    cB
    cM
    wph
    @22
    cA
    @1
    cun
    #
    cB
    wph
    @13
    @10
    @22
    @33
    wceq
    measssd.2
    @14
    cA
    @1
    cS
    cS
    uniprg
    syl2anc
    wph
    cA
    cB
    wss
    @33
    cB
    wceq
    measssd.4
    cA
    cB
    undif
    sylib
    eqtrd
    fveq2d
    wph
    cA
    @1
    @25
    @0
    vy
    @2
    cS
    cS
    @24
    cA
    wceq
    @25
    @0
    wceq
    wph
    @24
    cA
    cM
    fveq2
    adantl
    @24
    @1
    wceq
    @25
    @2
    wceq
    wph
    @24
    @1
    cM
    fveq2
    adantl
    measssd.2
    @14
    @20
    @15
    wph
    cA
    @1
    wceq
    #
    @0
    cc0
    wceq
    #
    @0
    cpnf
    wceq
    #
    wo
    wph
    @34
    wa
    #
    @35
    @36
    @37
    @0
    c0
    cM
    cfv
    #
    cc0
    @37
    cA
    c0
    cM
    @34
    cA
    c0
    wceq
    #
    wph
    @34
    cA
    @1
    wss
    @39
    cA
    @1
    eqimss
    cA
    cB
    ssdifeq0
    sylib
    adantl
    fveq2d
    wph
    @38
    cc0
    wceq
    #
    @34
    wph
    @9
    @40
    measssd.1
    cS
    cM
    measvnul
    syl
    adantr
    eqtrd
    orcd
    ex
    esumpr2
    3eqtr3d
    breqtrrd
end
