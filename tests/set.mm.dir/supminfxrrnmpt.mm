include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cv.mm"
include "cxne.mm"
include "wcel.mm"
include "crab.mm"
include "cinf.mm"
include "eqid.mm"
include "rnmptssd.mm"
include "supminfxr2.mm"
include "wss.mm"
include "wi.mm"
include "wral.mm"
include "wceq.mm"
include "wrex.mm"
include "cvv.mm"
include "wb.mm"
include "xnegex.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "wa.mm"
include "xnegneg.mm"
include "eqcomd.mm"
include "adantr.mm"
include "xnegeq.mm"
include "adantl.mm"
include "eqtrd.mm"
include "ex.mm"
include "reximdv.mm"
include "imp.mm"
include "simpl.mm"
include "elrnmptd.mm"
include "sylan2.mm"
include "rgen.mm"
include "rabss.mm"
include "biimpri.mm"
include "a1i.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfel.mm"
include "nfrab.mm"
include "eleq1d.mm"
include "xnegcld.mm"
include "syl.mm"
include "simpr.mm"
include "elrnmpt1d.mm"
include "eqeltrd.mm"
include "elrabd.mm"
include "rnmptssdf.mm"
include "eqssd.mm"
include "infeq1d.mm"
include "xnegeqd.mm"

theorem supminfxrrnmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume supminfxrrnmpt.x: |- F/ x ph
  assume supminfxrrnmpt.b: |- ( ( ph /\ x e. A ) -> B e. RR* )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  assert |- ( ph -> sup ( ran ( x e. A |-> B ) , RR* , < ) = -e inf ( ran ( x e. A |-> -e B ) , RR* , < ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    vy
    cv
    #
    cxne
    #
    @1
    wcel
    #
    vy
    cxr
    crab
    #
    cxr
    clt
    cinf
    #
    cxne
    vx
    cA
    cB
    cxne
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    #
    cxne
    wph
    vy
    @1
    wph
    vx
    cA
    cB
    cxr
    @0
    supminfxrrnmpt.x
    @0
    eqid
    #
    supminfxrrnmpt.b
    rnmptssd
    supminfxr2
    wph
    @6
    @10
    wph
    cxr
    @5
    @9
    clt
    wph
    @5
    @9
    @5
    @9
    wss
    #
    wph
    @4
    @2
    @9
    wcel
    #
    wi
    #
    vy
    cxr
    wral
    #
    @12
    @14
    vy
    cxr
    @2
    cxr
    wcel
    #
    @4
    @13
    @4
    @16
    @3
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @13
    @4
    @18
    @3
    cvv
    wcel
    @4
    @18
    wb
    @2
    xnegex
    vx
    cA
    cB
    @3
    @0
    cvv
    @11
    elrnmpt
    ax-mp
    biimpi
    @16
    @18
    wa
    vx
    cA
    @7
    @2
    @8
    cxr
    @8
    eqid
    #
    @16
    @18
    @2
    @7
    wceq
    #
    vx
    cA
    wrex
    @16
    @17
    @20
    vx
    cA
    @16
    @17
    @20
    @16
    @17
    wa
    @2
    @3
    cxne
    #
    @7
    @16
    @2
    @21
    wceq
    @17
    @16
    @21
    @2
    @2
    xnegneg
    eqcomd
    adantr
    @17
    @21
    @7
    wceq
    @16
    @3
    cB
    xnegeq
    adantl
    eqtrd
    ex
    reximdv
    imp
    @16
    @18
    simpl
    elrnmptd
    sylan2
    ex
    rgen
    @12
    @15
    @4
    vy
    cxr
    @9
    rabss
    biimpri
    ax-mp
    a1i
    wph
    vx
    cA
    @7
    @5
    @8
    supminfxrrnmpt.x
    @4
    vx
    vy
    cxr
    vx
    @3
    @1
    vx
    @3
    nfcv
    vx
    @0
    vx
    cA
    cB
    nfmpt1
    nfrn
    nfel
    vx
    cxr
    nfcv
    nfrab
    @19
    wph
    vx
    cv
    cA
    wcel
    #
    wa
    #
    @4
    @7
    cxne
    #
    @1
    wcel
    vy
    @7
    cxr
    @20
    @3
    @24
    @1
    @2
    @7
    xnegeq
    eleq1d
    @23
    cB
    supminfxrrnmpt.b
    xnegcld
    @23
    @24
    cB
    @1
    @23
    cB
    cxr
    wcel
    @24
    cB
    wceq
    supminfxrrnmpt.b
    cB
    xnegneg
    syl
    @23
    vx
    cA
    cB
    @0
    cxr
    @11
    wph
    @22
    simpr
    supminfxrrnmpt.b
    elrnmpt1d
    eqeltrd
    elrabd
    rnmptssdf
    eqssd
    infeq1d
    xnegeqd
    eqtrd
end
