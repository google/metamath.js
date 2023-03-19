include "cnacs.mm"
include "cfv.mm"
include "wcel.mm"
include "cacs.mm"
include "cv.mm"
include "wceq.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cima.mm"
include "isnacs.mm"
include "wss.mm"
include "wfn.mm"
include "wb.mm"
include "cmre.mm"
include "wf.mm"
include "acsmre.mm"
include "mrcf.mm"
include "ffn.mm"
include "3syl.mm"
include "inss1.mm"
include "fvelimab.mm"
include "sylancl.mm"
include "eqcom.mm"
include "rexbii.mm"
include "syl6rbbr.mm"
include "ralbidv.mm"
include "dfss3.mm"
include "syl6bbr.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "biantrurd.mm"
include "eqss.mm"
include "bitrd.mm"
include "pm5.32i.mm"
include "bitri.mm"

theorem isnacs2
  let cC: class C
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vg: setvar g
  let vs: setvar s
  let cS: class S
  let vx: setvar x
  assume isnacs.f: |- F = ( mrCls ` C )


  assert |- ( C e. ( NoeACS ` X ) <-> ( C e. ( ACS ` X ) /\ ( F " ( ~P X i^i Fin ) ) = C ) )

  proof
    cC
    cX
    cnacs
    cfv
    wcel
    cC
    cX
    cacs
    cfv
    wcel
    #
    vs
    cv
    #
    vg
    cv
    cF
    cfv
    #
    wceq
    #
    vg
    cX
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vs
    cC
    wral
    #
    wa
    @0
    cF
    @5
    cima
    #
    cC
    wceq
    #
    wa
    cC
    vg
    cF
    cX
    vs
    isnacs.f
    isnacs
    @0
    @7
    @9
    @0
    @7
    cC
    @8
    wss
    #
    @9
    @0
    @7
    @1
    @8
    wcel
    #
    vs
    cC
    wral
    @10
    @0
    @6
    @11
    vs
    cC
    @0
    @11
    @2
    @1
    wceq
    #
    vg
    @5
    wrex
    #
    @6
    @0
    cF
    @4
    wfn
    #
    @5
    @4
    wss
    @11
    @13
    wb
    @0
    cC
    cX
    cmre
    cfv
    wcel
    #
    @4
    cC
    cF
    wf
    #
    @14
    cC
    cX
    acsmre
    #
    cC
    cF
    cX
    isnacs.f
    mrcf
    #
    @4
    cC
    cF
    ffn
    3syl
    @4
    cfn
    inss1
    vg
    @4
    @5
    @1
    cF
    fvelimab
    sylancl
    @3
    @12
    vg
    @5
    @1
    @2
    eqcom
    rexbii
    syl6rbbr
    ralbidv
    vs
    cC
    @8
    dfss3
    syl6bbr
    @0
    @10
    @8
    cC
    wss
    #
    @10
    wa
    @9
    @0
    @19
    @10
    @0
    @8
    cF
    crn
    #
    cC
    cF
    @5
    imassrn
    @0
    @15
    @16
    @20
    cC
    wss
    @17
    @18
    @4
    cC
    cF
    frn
    3syl
    syl5ss
    biantrurd
    @8
    cC
    eqss
    syl6bbr
    bitrd
    pm5.32i
    bitri
end
