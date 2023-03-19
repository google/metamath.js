include "cc.mm"
include "wf.mm"
include "wcel.mm"
include "w3a.mm"
include "cfdiv.mm"
include "co.mm"
include "cc0.mm"
include "csupp.mm"
include "cres.mm"
include "cdiv.mm"
include "cof.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "wceq.mm"
include "fex.mm"
include "3adant2.mm"
include "3adant1.mm"
include "wa.mm"
include "fdivval.mm"
include "offres.mm"
include "eqtrd.mm"
include "syl2anc.mm"
include "wfn.mm"
include "wss.mm"
include "ffn.mm"
include "3ad2ant1.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "eqcomd.mm"
include "3ad2ant2.mm"
include "syl5sseqr.mm"
include "fnssres.mm"
include "ovexd.mm"
include "inidm.mm"
include "fvres.mm"
include "adantl.mm"
include "offval.mm"

theorem fdivmpt
  let vx: setvar x
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vk: setvar k

  disjoint A x
  disjoint F x
  disjoint G x
  disjoint V x
  disjoint k x
  assert |- ( ( F : A --> CC /\ G : A --> CC /\ A e. V ) -> ( F /_f G ) = ( x e. ( G supp 0 ) |-> ( ( F ` x ) / ( G ` x ) ) ) )

  proof
    cA
    cc
    cF
    wf
    #
    cA
    cc
    cG
    wf
    #
    cA
    cV
    wcel
    #
    w3a
    #
    cF
    cG
    cfdiv
    co
    #
    cF
    cG
    cc0
    csupp
    co
    #
    cres
    #
    cG
    @5
    cres
    #
    cdiv
    cof
    #
    co
    #
    vx
    @5
    vx
    cv
    #
    cF
    cfv
    #
    @10
    cG
    cfv
    #
    cdiv
    co
    cmpt
    @3
    cF
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    @4
    @9
    wceq
    @0
    @2
    @13
    @1
    cA
    cc
    cV
    cF
    fex
    3adant2
    @1
    @2
    @14
    @0
    cA
    cc
    cV
    cG
    fex
    3adant1
    @13
    @14
    wa
    @4
    cF
    cG
    @8
    co
    @5
    cres
    @9
    cF
    cG
    cvv
    cvv
    fdivval
    @5
    cdiv
    cF
    cG
    cvv
    cvv
    offres
    eqtrd
    syl2anc
    @3
    vx
    @5
    @5
    @11
    @12
    cdiv
    @5
    @6
    @7
    cvv
    cvv
    @3
    cF
    cA
    wfn
    #
    @5
    cA
    wss
    #
    @6
    @5
    wfn
    @0
    @1
    @15
    @2
    cA
    cc
    cF
    ffn
    3ad2ant1
    @3
    cG
    cdm
    #
    @5
    cA
    cG
    cc0
    suppssdm
    @1
    @0
    cA
    @17
    wceq
    @2
    @1
    @17
    cA
    cA
    cc
    cG
    fdm
    eqcomd
    3ad2ant2
    syl5sseqr
    #
    cA
    @5
    cF
    fnssres
    syl2anc
    @3
    cG
    cA
    wfn
    #
    @16
    @7
    @5
    wfn
    @1
    @0
    @19
    @2
    cA
    cc
    cG
    ffn
    3ad2ant2
    @18
    cA
    @5
    cG
    fnssres
    syl2anc
    @3
    cG
    cc0
    csupp
    ovexd
    #
    @20
    @5
    inidm
    @10
    @5
    wcel
    #
    @10
    @6
    cfv
    @11
    wceq
    @3
    @10
    @5
    cF
    fvres
    adantl
    @21
    @10
    @7
    cfv
    @12
    wceq
    @3
    @10
    @5
    cG
    fvres
    adantl
    offval
    eqtrd
end
