include "cle.mm"
include "ccnv.mm"
include "cr.mm"
include "cv.mm"
include "wbr.mm"
include "crab.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "ccld.mm"
include "clt.mm"
include "wa.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "simpr.mm"
include "adantr.mm"
include "brcnvg.mm"
include "syl2anc.mm"
include "pm5.32da.mm"
include "rexr.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "ltpnf.mm"
include "jca.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "xrre3.mm"
include "syl22anc.mm"
include "impbida.mm"
include "bitrd.mm"
include "rabbidva2.mm"
include "wceq.mm"
include "rexrd.mm"
include "pnfxr.mm"
include "icoval.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "icopnfcld.mm"
include "syl.mm"
include "eqeltrd.mm"
include "orrvccel.mm"

theorem orvcgteel
  let wph: wff ph
  let cA: class A
  let cP: class P
  let cX: class X
  let vx: setvar x
  assume orvcgteel.1: |- ( ph -> P e. Prob )
  assume orvcgteel.2: |- ( ph -> X e. ( rRndVar ` P ) )
  assume orvcgteel.3: |- ( ph -> A e. RR )


  assert |- ( ph -> ( X oRVC `' <_ A ) e. dom P )

  proof
    wph
    vx
    cA
    cP
    cle
    ccnv
    #
    cr
    cX
    orvcgteel.1
    orvcgteel.2
    orvcgteel.3
    wph
    vx
    cv
    #
    cA
    @0
    wbr
    #
    vx
    cr
    crab
    #
    cA
    cpnf
    cico
    co
    #
    cioo
    crn
    ctg
    cfv
    ccld
    cfv
    #
    wph
    @3
    cA
    @1
    cle
    wbr
    #
    @1
    cpnf
    clt
    wbr
    #
    wa
    #
    vx
    cxr
    crab
    #
    @4
    wph
    @2
    @8
    vx
    cr
    cxr
    wph
    @1
    cr
    wcel
    #
    @2
    wa
    @10
    @6
    wa
    #
    @1
    cxr
    wcel
    #
    @8
    wa
    #
    wph
    @10
    @2
    @6
    wph
    @10
    wa
    @10
    cA
    cr
    wcel
    #
    @2
    @6
    wb
    wph
    @10
    simpr
    wph
    @14
    @10
    orvcgteel.3
    adantr
    @1
    cA
    cr
    cr
    cle
    brcnvg
    syl2anc
    pm5.32da
    wph
    @11
    @13
    wph
    @11
    wa
    #
    @12
    @8
    @10
    @12
    wph
    @6
    @1
    rexr
    ad2antrl
    @15
    @6
    @7
    wph
    @10
    @6
    simprr
    @10
    @7
    wph
    @6
    @1
    ltpnf
    ad2antrl
    jca
    jca
    wph
    @13
    wa
    #
    @10
    @6
    @16
    @12
    @14
    @6
    @7
    @10
    wph
    @12
    @8
    simprl
    wph
    @14
    @13
    orvcgteel.3
    adantr
    wph
    @12
    @6
    @7
    simprrl
    #
    wph
    @12
    @6
    @7
    simprrr
    @1
    cA
    xrre3
    syl22anc
    @17
    jca
    impbida
    bitrd
    rabbidva2
    wph
    cA
    cxr
    wcel
    cpnf
    cxr
    wcel
    @4
    @9
    wceq
    wph
    cA
    orvcgteel.3
    rexrd
    pnfxr
    vx
    cA
    cpnf
    icoval
    sylancl
    eqtr4d
    wph
    @14
    @4
    @5
    wcel
    orvcgteel.3
    cA
    icopnfcld
    syl
    eqeltrd
    orrvccel
end
