include "cdif.mm"
include "ccarsg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "cin.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "cpw.mm"
include "wral.mm"
include "wa.mm"
include "difssd.mm"
include "indif2.mm"
include "elpwi.mm"
include "adantl.mm"
include "df-ss.mm"
include "sylib.mm"
include "difeq1d.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "cun.mm"
include "difdif2.mm"
include "c0.mm"
include "ssdif0.mm"
include "uneq1d.mm"
include "uncom.mm"
include "un0.mm"
include "eqtr3i.mm"
include "syl6eq.mm"
include "oveq12d.mm"
include "cxr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "iccssxr.mm"
include "wf.mm"
include "adantr.mm"
include "simpr.mm"
include "elpwdifcl.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "elpwincl1.mm"
include "xaddcom.mm"
include "syl2anc.mm"
include "elcarsg.mm"
include "mpbid.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "3eqtrd.mm"
include "ralrimiva.mm"
include "jca.mm"
include "mpbird.mm"

theorem difelcarsg
  let wph: wff ph
  let cA: class A
  let cM: class M
  let cO: class O
  let cV: class V
  let va: setvar a
  let ve: setvar e
  let vm: setvar m
  assume carsgval.1: |- ( ph -> O e. V )
  assume carsgval.2: |- ( ph -> M : ~P O --> ( 0 [,] +oo ) )
  assume difelcarsg.1: |- ( ph -> A e. ( toCaraSiga ` M ) )


  assert |- ( ph -> ( O \ A ) e. ( toCaraSiga ` M ) )

  proof
    wph
    cO
    cA
    cdif
    #
    cM
    ccarsg
    cfv
    #
    wcel
    @0
    cO
    wss
    #
    ve
    cv
    #
    @0
    cin
    #
    cM
    cfv
    #
    @3
    @0
    cdif
    #
    cM
    cfv
    #
    cxad
    co
    #
    @3
    cM
    cfv
    #
    wceq
    #
    ve
    cO
    cpw
    #
    wral
    #
    wa
    wph
    @2
    @12
    wph
    cO
    cA
    difssd
    wph
    @10
    ve
    @11
    wph
    @3
    @11
    wcel
    #
    wa
    #
    @8
    @3
    cA
    cdif
    #
    cM
    cfv
    #
    @3
    cA
    cin
    #
    cM
    cfv
    #
    cxad
    co
    #
    @18
    @16
    cxad
    co
    #
    @9
    @14
    @5
    @16
    @7
    @18
    cxad
    @14
    @4
    @15
    cM
    @14
    @4
    @3
    cO
    cin
    #
    cA
    cdif
    @15
    @3
    cO
    cA
    indif2
    @14
    @21
    @3
    cA
    @14
    @3
    cO
    wss
    #
    @21
    @3
    wceq
    @13
    @22
    wph
    @3
    cO
    elpwi
    adantl
    #
    @3
    cO
    df-ss
    sylib
    difeq1d
    syl5eq
    fveq2d
    @14
    @6
    @17
    cM
    @14
    @6
    @3
    cO
    cdif
    #
    @17
    cun
    #
    @17
    @3
    cO
    cA
    difdif2
    @14
    @25
    c0
    @17
    cun
    #
    @17
    @14
    @24
    c0
    @17
    @14
    @22
    @24
    c0
    wceq
    @23
    @3
    cO
    ssdif0
    sylib
    uneq1d
    @17
    c0
    cun
    @26
    @17
    @17
    c0
    uncom
    @17
    un0
    eqtr3i
    syl6eq
    syl5eq
    fveq2d
    oveq12d
    @14
    @16
    cxr
    wcel
    @18
    cxr
    wcel
    @19
    @20
    wceq
    @14
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @16
    cc0
    cpnf
    iccssxr
    #
    @14
    @11
    @27
    @15
    cM
    wph
    @11
    @27
    cM
    wf
    @13
    carsgval.2
    adantr
    #
    @14
    @3
    cA
    cO
    wph
    @13
    simpr
    #
    elpwdifcl
    ffvelrnd
    sseldi
    @14
    @27
    cxr
    @18
    @28
    @14
    @11
    @27
    @17
    cM
    @29
    @14
    @3
    cA
    cO
    @30
    elpwincl1
    ffvelrnd
    sseldi
    @16
    @18
    xaddcom
    syl2anc
    wph
    @20
    @9
    wceq
    #
    ve
    @11
    wph
    cA
    cO
    wss
    #
    @31
    ve
    @11
    wral
    #
    wph
    cA
    @1
    wcel
    @32
    @33
    wa
    difelcarsg.1
    wph
    cA
    ve
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    elcarsg
    mpbid
    simprd
    r19.21bi
    3eqtrd
    ralrimiva
    jca
    wph
    @0
    ve
    cM
    cO
    cV
    carsgval.1
    carsgval.2
    elcarsg
    mpbird
end
