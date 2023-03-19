include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cfg.mm"
include "co.mm"
include "crest.mm"
include "cv.mm"
include "cin.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "cfbas.mm"
include "cpw.mm"
include "filfbas.mm"
include "3ad2ant1.mm"
include "filsspw.mm"
include "simp2.mm"
include "sspwb.mm"
include "sylib.mm"
include "sstrd.mm"
include "simp3.mm"
include "fbasweak.mm"
include "syl3anc.mm"
include "fgcl.mm"
include "syl.mm"
include "filtop.mm"
include "restval.mm"
include "syl2anc.mm"
include "wf.mm"
include "wa.mm"
include "wrex.mm"
include "wb.mm"
include "elfg.mm"
include "simplbda.mm"
include "simpll1.mm"
include "simprl.mm"
include "inss2.mm"
include "a1i.mm"
include "simprr.mm"
include "filelss.mm"
include "3ad2antl1.mm"
include "ad2ant2r.mm"
include "ssind.mm"
include "filss.mm"
include "syl13anc.mm"
include "rexlimddv.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "eqsstrd.mm"
include "df-ss.mm"
include "adantr.mm"
include "ssfg.mm"
include "sselda.mm"
include "elrestr.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem trfg
  let cA: class A
  let cF: class F
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( F e. ( Fil ` A ) /\ A C_ X /\ X e. V ) -> ( ( X filGen F ) |`t A ) = F )

  proof
    cF
    cA
    cfil
    cfv
    wcel
    #
    cA
    cX
    wss
    #
    cX
    cV
    wcel
    #
    w3a
    #
    cX
    cF
    cfg
    co
    #
    cA
    crest
    co
    #
    cF
    @3
    @5
    vx
    @4
    vx
    cv
    #
    cA
    cin
    #
    cmpt
    #
    crn
    #
    cF
    @3
    @4
    cX
    cfil
    cfv
    #
    wcel
    #
    cA
    cF
    wcel
    #
    @5
    @9
    wceq
    @3
    cF
    cX
    cfbas
    cfv
    wcel
    #
    @11
    @3
    cF
    cA
    cfbas
    cfv
    wcel
    #
    cF
    cX
    cpw
    #
    wss
    @2
    @13
    @0
    @1
    @14
    @2
    cF
    cA
    filfbas
    3ad2ant1
    @3
    cF
    cA
    cpw
    #
    @15
    @0
    @1
    cF
    @16
    wss
    @2
    cF
    cA
    filsspw
    3ad2ant1
    @3
    @1
    @16
    @15
    wss
    @0
    @1
    @2
    simp2
    cA
    cX
    sspwb
    sylib
    sstrd
    @0
    @1
    @2
    simp3
    cF
    cV
    cA
    cX
    fbasweak
    syl3anc
    #
    cF
    cX
    fgcl
    syl
    #
    @0
    @1
    @12
    @2
    cF
    cA
    filtop
    3ad2ant1
    #
    vx
    cA
    @4
    @10
    cF
    restval
    syl2anc
    @3
    @4
    cF
    @8
    wf
    @9
    cF
    wss
    @3
    vx
    @4
    @7
    cF
    @8
    @3
    @6
    @4
    wcel
    #
    wa
    #
    vy
    cv
    #
    @6
    wss
    #
    @7
    cF
    wcel
    #
    vy
    cF
    @3
    @20
    @6
    cX
    wss
    #
    @23
    vy
    cF
    wrex
    #
    @3
    @13
    @20
    @25
    @26
    wa
    wb
    @17
    vy
    @6
    cF
    cX
    elfg
    syl
    simplbda
    @21
    @22
    cF
    wcel
    #
    @23
    wa
    #
    wa
    #
    @0
    @27
    @7
    cA
    wss
    #
    @22
    @7
    wss
    @24
    @0
    @1
    @2
    @20
    @28
    simpll1
    @21
    @27
    @23
    simprl
    @30
    @29
    @6
    cA
    inss2
    a1i
    @29
    @22
    @6
    cA
    @21
    @27
    @23
    simprr
    @3
    @27
    @22
    cA
    wss
    #
    @20
    @23
    @0
    @1
    @27
    @31
    @2
    @22
    cF
    cA
    filelss
    3ad2antl1
    ad2ant2r
    ssind
    @22
    @7
    cF
    cA
    filss
    syl13anc
    rexlimddv
    @8
    eqid
    fmptd
    @4
    cF
    @8
    frn
    syl
    eqsstrd
    @3
    vx
    cF
    @5
    @3
    @6
    cF
    wcel
    #
    @6
    @5
    wcel
    @3
    @32
    wa
    #
    @7
    @6
    @5
    @33
    @6
    cA
    wss
    #
    @7
    @6
    wceq
    @0
    @1
    @32
    @34
    @2
    @6
    cF
    cA
    filelss
    3ad2antl1
    @6
    cA
    df-ss
    sylib
    @33
    @11
    @12
    @20
    @7
    @5
    wcel
    @3
    @11
    @32
    @18
    adantr
    @3
    @12
    @32
    @19
    adantr
    @3
    cF
    @4
    @6
    @3
    @13
    cF
    @4
    wss
    @17
    cF
    cX
    ssfg
    syl
    sselda
    @6
    cA
    @4
    @10
    cF
    elrestr
    syl3anc
    eqeltrrd
    ex
    ssrdv
    eqssd
end
