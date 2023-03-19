include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cdm.mm"
include "wf.mm"
include "wa.mm"
include "cc0.mm"
include "cfzo.mm"
include "cfv.mm"
include "caddc.mm"
include "wceq.mm"
include "chash.mm"
include "cvv.mm"
include "wfn.mm"
include "wi.mm"
include "ffn.mm"
include "fseq1hash.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "syl.mm"
include "sylan2.mm"
include "imp.mm"
include "fvex.mm"
include "cv.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "ex.mm"

theorem fargshiftfv
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
  assert |- ( ( N e. NN0 /\ F : ( 1 ... N ) --> dom E ) -> ( X e. ( 0 ..^ N ) -> ( G ` X ) = ( F ` ( X + 1 ) ) ) )

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
    cX
    cc0
    cN
    cfzo
    co
    #
    wcel
    #
    cX
    cG
    cfv
    cX
    c1
    caddc
    co
    #
    cF
    cfv
    #
    wceq
    #
    @4
    @6
    wa
    cX
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wcel
    #
    @8
    cvv
    wcel
    @9
    @4
    @6
    @12
    @3
    @0
    cF
    @1
    wfn
    #
    @6
    @12
    wi
    #
    @1
    @2
    cF
    ffn
    @0
    @13
    wa
    @10
    cN
    wceq
    #
    @14
    cF
    cN
    fseq1hash
    @15
    @6
    @12
    @15
    @5
    @11
    cX
    @5
    @11
    wceq
    cN
    @10
    cN
    @10
    cc0
    cfzo
    oveq2
    eqcoms
    eleq2d
    biimpd
    syl
    sylan2
    imp
    @7
    cF
    fvex
    vx
    cX
    vx
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    @8
    @11
    cvv
    cG
    @16
    cX
    wceq
    @17
    @7
    cF
    @16
    cX
    c1
    caddc
    oveq1
    fveq2d
    fargshift.g
    fvmptg
    sylancl
    ex
end
