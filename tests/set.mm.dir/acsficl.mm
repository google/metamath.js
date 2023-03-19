include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cpw.mm"
include "cv.mm"
include "cfn.mm"
include "cin.mm"
include "cima.mm"
include "cuni.mm"
include "wceq.mm"
include "wral.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "elpw2g.mm"
include "syl.mm"
include "biimpar.mm"
include "cmre.mm"
include "cipo.mm"
include "cdrs.mm"
include "wi.mm"
include "isacs3lem.mm"
include "isacs4lem.mm"
include "isacs5lem.mm"
include "3syl.mm"
include "simprd.mm"
include "adantr.mm"
include "fveq2.mm"
include "pweq.mm"
include "ineq1d.mm"
include "imaeq2d.mm"
include "unieqd.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "syl2anc.mm"

theorem acsficl
  let cC: class C
  let cS: class S
  let cF: class F
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  assume acsdrscl.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( ACS ` X ) /\ S C_ X ) -> ( F ` S ) = U. ( F " ( ~P S i^i Fin ) ) )

  proof
    cC
    cX
    cacs
    cfv
    wcel
    #
    cS
    cX
    wss
    #
    wa
    cS
    cX
    cpw
    #
    wcel
    #
    vs
    cv
    #
    cF
    cfv
    #
    cF
    @4
    cpw
    #
    cfn
    cin
    #
    cima
    #
    cuni
    #
    wceq
    #
    vs
    @2
    wral
    #
    cS
    cF
    cfv
    #
    cF
    cS
    cpw
    #
    cfn
    cin
    #
    cima
    #
    cuni
    #
    wceq
    #
    @0
    @3
    @1
    @0
    cX
    cacs
    cdm
    #
    wcel
    @3
    @1
    wb
    cC
    cX
    cacs
    elfvdm
    cS
    cX
    @18
    elpw2g
    syl
    biimpar
    @0
    @11
    @1
    @0
    cC
    cX
    cmre
    cfv
    wcel
    #
    @11
    @0
    @19
    @4
    cipo
    cfv
    cdrs
    wcel
    @4
    cuni
    cC
    wcel
    wi
    vs
    cC
    cpw
    wral
    wa
    @19
    vt
    cv
    #
    cipo
    cfv
    cdrs
    wcel
    @20
    cuni
    cF
    cfv
    cF
    @20
    cima
    cuni
    wceq
    wi
    vt
    @2
    cpw
    wral
    wa
    @19
    @11
    wa
    cC
    cX
    vs
    isacs3lem
    vt
    cC
    cF
    cX
    vs
    acsdrscl.f
    isacs4lem
    vt
    cC
    cF
    cX
    vs
    acsdrscl.f
    isacs5lem
    3syl
    simprd
    adantr
    @10
    @17
    vs
    cS
    @2
    @4
    cS
    wceq
    #
    @5
    @12
    @9
    @16
    @4
    cS
    cF
    fveq2
    @21
    @8
    @15
    @21
    @7
    @14
    cF
    @21
    @6
    @13
    cfn
    @4
    cS
    pweq
    ineq1d
    imaeq2d
    unieqd
    eqeq12d
    rspcva
    syl2anc
end
