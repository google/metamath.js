include "cmre.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cpr.mm"
include "cuni.mm"
include "cima.mm"
include "cun.mm"
include "cpw.mm"
include "wceq.mm"
include "simp1.mm"
include "wb.mm"
include "mre1cl.mm"
include "elpw2g.mm"
include "syl.mm"
include "biimpar.mm"
include "3adant3.mm"
include "3adant2.mm"
include "prssi.mm"
include "syl2anc.mm"
include "mrcuni.mm"
include "uniprg.mm"
include "fveq2d.mm"
include "wfn.mm"
include "wf.mm"
include "mrcf.mm"
include "ffn.mm"
include "3ad2ant1.mm"
include "fnimapr.mm"
include "syl3anc.mm"
include "unieqd.mm"
include "fvex.mm"
include "unipr.mm"
include "syl6eq.mm"
include "3eqtr3d.mm"

theorem mrcun
  let cC: class C
  let cU: class U
  let cF: class F
  let cV: class V
  let cX: class X
  let vc: setvar c
  let vx: setvar x
  let vs: setvar s
  assume mrcfval.f: |- F = ( mrCls ` C )


  assert |- ( ( C e. ( Moore ` X ) /\ U C_ X /\ V C_ X ) -> ( F ` ( U u. V ) ) = ( F ` ( ( F ` U ) u. ( F ` V ) ) ) )

  proof
    cC
    cX
    cmre
    cfv
    wcel
    #
    cU
    cX
    wss
    #
    cV
    cX
    wss
    #
    w3a
    #
    cU
    cV
    cpr
    #
    cuni
    #
    cF
    cfv
    #
    cF
    @4
    cima
    #
    cuni
    #
    cF
    cfv
    #
    cU
    cV
    cun
    #
    cF
    cfv
    cU
    cF
    cfv
    #
    cV
    cF
    cfv
    #
    cun
    #
    cF
    cfv
    @3
    @0
    @4
    cX
    cpw
    #
    wss
    #
    @6
    @9
    wceq
    @0
    @1
    @2
    simp1
    @3
    cU
    @14
    wcel
    #
    cV
    @14
    wcel
    #
    @15
    @0
    @1
    @16
    @2
    @0
    @16
    @1
    @0
    cX
    cC
    wcel
    #
    @16
    @1
    wb
    cC
    cX
    mre1cl
    #
    cU
    cX
    cC
    elpw2g
    syl
    biimpar
    3adant3
    #
    @0
    @2
    @17
    @1
    @0
    @17
    @2
    @0
    @18
    @17
    @2
    wb
    @19
    cV
    cX
    cC
    elpw2g
    syl
    biimpar
    3adant2
    #
    cU
    cV
    @14
    prssi
    syl2anc
    cC
    @4
    cF
    cX
    mrcfval.f
    mrcuni
    syl2anc
    @3
    @5
    @10
    cF
    @3
    @16
    @17
    @5
    @10
    wceq
    @20
    @21
    cU
    cV
    @14
    @14
    uniprg
    syl2anc
    fveq2d
    @3
    @8
    @13
    cF
    @3
    @8
    @11
    @12
    cpr
    #
    cuni
    @13
    @3
    @7
    @22
    @3
    cF
    @14
    wfn
    #
    @16
    @17
    @7
    @22
    wceq
    @0
    @1
    @23
    @2
    @0
    @14
    cC
    cF
    wf
    @23
    cC
    cF
    cX
    mrcfval.f
    mrcf
    @14
    cC
    cF
    ffn
    syl
    3ad2ant1
    @20
    @21
    @14
    cU
    cV
    cF
    fnimapr
    syl3anc
    unieqd
    @11
    @12
    cU
    cF
    fvex
    cV
    cF
    fvex
    unipr
    syl6eq
    fveq2d
    3eqtr3d
end
