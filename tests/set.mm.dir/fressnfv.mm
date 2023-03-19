include "wcel.mm"
include "wfn.mm"
include "csn.mm"
include "cres.mm"
include "wf.mm"
include "cfv.mm"
include "wb.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "sneq.mm"
include "reseq2.mm"
include "feq1d.mm"
include "feq2.mm"
include "bitrd.mm"
include "syl.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "wa.mm"
include "cop.mm"
include "fnressn.mm"
include "vsnid.mm"
include "fvres.mm"
include "ax-mp.mm"
include "opeq2i.mm"
include "sneqi.mm"
include "eqeq2i.mm"
include "vex.mm"
include "fsn2.mm"
include "eleq1i.mm"
include "iba.mm"
include "syl5rbbr.mm"
include "syl5bb.mm"
include "sylbir.mm"
include "expcom.mm"
include "vtoclga.mm"
include "impcom.mm"

theorem fressnfv
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x


  assert |- ( ( F Fn A /\ B e. A ) -> ( ( F |` { B } ) : { B } --> C <-> ( F ` B ) e. C ) )

  proof
    cB
    cA
    wcel
    cF
    cA
    wfn
    #
    cB
    csn
    #
    cC
    cF
    @1
    cres
    #
    wf
    #
    cB
    cF
    cfv
    #
    cC
    wcel
    #
    wb
    #
    @0
    vx
    cv
    #
    csn
    #
    cC
    cF
    @8
    cres
    #
    wf
    #
    @7
    cF
    cfv
    #
    cC
    wcel
    #
    wb
    #
    wi
    @0
    @6
    wi
    vx
    cB
    cA
    @7
    cB
    wceq
    #
    @13
    @6
    @0
    @14
    @10
    @3
    @12
    @5
    @14
    @8
    @1
    wceq
    #
    @10
    @3
    wb
    @7
    cB
    sneq
    @15
    @10
    @8
    cC
    @2
    wf
    @3
    @15
    @8
    cC
    @9
    @2
    @8
    @1
    cF
    reseq2
    feq1d
    @8
    @1
    cC
    @2
    feq2
    bitrd
    syl
    @14
    @11
    @4
    cC
    @7
    cB
    cF
    fveq2
    eleq1d
    bibi12d
    imbi2d
    @0
    @7
    cA
    wcel
    #
    @13
    @0
    @16
    wa
    @9
    @7
    @11
    cop
    #
    csn
    #
    wceq
    #
    @13
    cA
    @7
    cF
    fnressn
    @19
    @9
    @7
    @7
    @9
    cfv
    #
    cop
    #
    csn
    #
    wceq
    #
    @13
    @22
    @18
    @9
    @21
    @17
    @20
    @11
    @7
    @7
    @8
    wcel
    @20
    @11
    wceq
    vx
    vsnid
    @7
    @8
    cF
    fvres
    ax-mp
    #
    opeq2i
    sneqi
    eqeq2i
    @10
    @20
    cC
    wcel
    #
    @23
    wa
    #
    @23
    @12
    @7
    cC
    @9
    vx
    vex
    fsn2
    @12
    @25
    @23
    @26
    @20
    @11
    cC
    @24
    eleq1i
    @23
    @25
    iba
    syl5rbbr
    syl5bb
    sylbir
    syl
    expcom
    vtoclga
    impcom
end
