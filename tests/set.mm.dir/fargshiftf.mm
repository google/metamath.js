include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cdm.mm"
include "wf.mm"
include "wa.mm"
include "cv.mm"
include "caddc.mm"
include "cfv.mm"
include "cc0.mm"
include "chash.mm"
include "cfzo.mm"
include "wral.mm"
include "wceq.mm"
include "wfn.mm"
include "ffn.mm"
include "fseq1hash.mm"
include "sylan2.mm"
include "wb.mm"
include "eleq1.mm"
include "oveq2.mm"
include "feq2d.mm"
include "anbi12d.mm"
include "eqcoms.mm"
include "wi.mm"
include "fz0add1fz1.mm"
include "ffvelrn.mm"
include "expcom.mm"
include "syl.mm"
include "impancom.mm"
include "ralrimiv.mm"
include "syl6bi.mm"
include "mpcom.mm"
include "fmpt.mm"
include "sylib.mm"

theorem fargshiftf
  let vx: setvar x
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cX: class X
  let vk: setvar k
  assume fargshift.g: |- G = ( x e. ( 0 ..^ ( # ` F ) ) |-> ( F ` ( x + 1 ) ) )

  disjoint F x
  disjoint E x
  disjoint X x
  disjoint k x
  assert |- ( ( N e. NN0 /\ F : ( 1 ... N ) --> dom E ) -> G : ( 0 ..^ ( # ` F ) ) --> dom E )

  proof
    cN
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    cE
    cdm
    #
    cF
    wf
    #
    wa
    #
    vx
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @2
    wcel
    #
    vx
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    @10
    @2
    cG
    wf
    @9
    cN
    wceq
    #
    @4
    @11
    @3
    @0
    cF
    @1
    wfn
    @12
    @1
    @2
    cF
    ffn
    cF
    cN
    fseq1hash
    sylan2
    @12
    @4
    @9
    cn0
    wcel
    #
    c1
    @9
    cfz
    co
    #
    @2
    cF
    wf
    #
    wa
    #
    @11
    @4
    @16
    wb
    cN
    @9
    cN
    @9
    wceq
    #
    @0
    @13
    @3
    @15
    cN
    @9
    cn0
    eleq1
    @17
    @1
    @14
    @2
    cF
    cN
    @9
    c1
    cfz
    oveq2
    feq2d
    anbi12d
    eqcoms
    @16
    @8
    vx
    @10
    @13
    @5
    @10
    wcel
    #
    @15
    @8
    @13
    @18
    wa
    @6
    @14
    wcel
    #
    @15
    @8
    wi
    @9
    @5
    fz0add1fz1
    @15
    @19
    @8
    @14
    @2
    @6
    cF
    ffvelrn
    expcom
    syl
    impancom
    ralrimiv
    syl6bi
    mpcom
    vx
    @10
    @2
    @7
    cG
    fargshift.g
    fmpt
    sylib
end
