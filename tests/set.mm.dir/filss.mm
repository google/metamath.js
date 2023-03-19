include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wa.mm"
include "cv.mm"
include "cpw.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "cfbas.mm"
include "isfil.mm"
include "simprbi.mm"
include "adantr.mm"
include "cdm.mm"
include "elfvdm.mm"
include "simp2.mm"
include "elpw2g.mm"
include "biimpar.mm"
include "syl2an.mm"
include "simpr1.mm"
include "simpr3.mm"
include "wb.mm"
include "elpwg.mm"
include "syl.mm"
include "mpbird.mm"
include "inelcm.mm"
include "syl2anc.mm"
include "wceq.mm"
include "pweq.mm"
include "ineq2d.mm"
include "neeq1d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "syl3c.mm"

theorem filss
  let cA: class A
  let cB: class B
  let cF: class F
  let cX: class X
  let vx: setvar x


  assert |- ( ( F e. ( Fil ` X ) /\ ( A e. F /\ B C_ X /\ A C_ B ) ) -> B e. F )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    #
    cA
    cF
    wcel
    #
    cB
    cX
    wss
    #
    cA
    cB
    wss
    #
    w3a
    #
    wa
    #
    cF
    vx
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    @6
    cF
    wcel
    #
    wi
    #
    vx
    cX
    cpw
    #
    wral
    #
    cB
    @12
    wcel
    #
    cF
    cB
    cpw
    #
    cin
    #
    c0
    wne
    #
    cB
    cF
    wcel
    #
    @0
    @13
    @4
    @0
    cF
    cX
    cfbas
    cfv
    wcel
    @13
    vx
    cF
    cX
    isfil
    simprbi
    adantr
    @0
    cX
    cfil
    cdm
    #
    wcel
    #
    @2
    @14
    @4
    cF
    cX
    cfil
    elfvdm
    @1
    @2
    @3
    simp2
    @20
    @14
    @2
    cB
    cX
    @19
    elpw2g
    biimpar
    syl2an
    @5
    @1
    cA
    @15
    wcel
    #
    @17
    @0
    @1
    @2
    @3
    simpr1
    #
    @5
    @21
    @3
    @0
    @1
    @2
    @3
    simpr3
    @5
    @1
    @21
    @3
    wb
    @22
    cA
    cB
    cF
    elpwg
    syl
    mpbird
    cA
    cF
    @15
    inelcm
    syl2anc
    @11
    @17
    @18
    wi
    vx
    cB
    @12
    @6
    cB
    wceq
    #
    @9
    @17
    @10
    @18
    @23
    @8
    @16
    c0
    @23
    @7
    @15
    cF
    @6
    cB
    pweq
    ineq2d
    neeq1d
    @6
    cB
    cF
    eleq1
    imbi12d
    rspccv
    syl3c
end
