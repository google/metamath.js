include "cvv.mm"
include "wcel.mm"
include "cmzp.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "cres.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cfn.mm"
include "elfvex.mm"
include "wi.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "sseq2.mm"
include "oveq2.mm"
include "mpteq1d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "2rexbidv.mm"
include "imbi12d.mm"
include "vex.mm"
include "mzpcompact2lem.mm"
include "vtoclg.mm"
include "mpcom.mm"

theorem mzpcompact2
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint A a
  disjoint A b
  disjoint a b
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint a c
  disjoint b c
  disjoint A d
  disjoint a d
  disjoint b d
  disjoint B d
  disjoint c d
  assert |- ( A e. ( mzPoly ` B ) -> E. a e. Fin E. b e. ( mzPoly ` a ) ( a C_ B /\ A = ( c e. ( ZZ ^m B ) |-> ( b ` ( c |` a ) ) ) ) )

  proof
    cB
    cvv
    wcel
    cA
    cB
    cmzp
    cfv
    #
    wcel
    #
    va
    cv
    #
    cB
    wss
    #
    cA
    vc
    cz
    cB
    cmap
    co
    #
    vc
    cv
    @2
    cres
    vb
    cv
    cfv
    #
    cmpt
    #
    wceq
    #
    wa
    #
    vb
    @2
    cmzp
    cfv
    #
    wrex
    va
    cfn
    wrex
    #
    cA
    cB
    cmzp
    elfvex
    cA
    vd
    cv
    #
    cmzp
    cfv
    #
    wcel
    #
    @2
    @11
    wss
    #
    cA
    vc
    cz
    @11
    cmap
    co
    #
    @5
    cmpt
    #
    wceq
    #
    wa
    #
    vb
    @9
    wrex
    va
    cfn
    wrex
    #
    wi
    @1
    @10
    wi
    vd
    cB
    cvv
    @11
    cB
    wceq
    #
    @13
    @1
    @19
    @10
    @20
    @12
    @0
    cA
    @11
    cB
    cmzp
    fveq2
    eleq2d
    @20
    @18
    @8
    va
    vb
    cfn
    @9
    @20
    @14
    @3
    @17
    @7
    @11
    cB
    @2
    sseq2
    @20
    @16
    @6
    cA
    @20
    vc
    @15
    @4
    @5
    @11
    cB
    cz
    cmap
    oveq2
    mpteq1d
    eqeq2d
    anbi12d
    2rexbidv
    imbi12d
    cA
    @11
    va
    vb
    vc
    vd
    vex
    mzpcompact2lem
    vtoclg
    mpcom
end
