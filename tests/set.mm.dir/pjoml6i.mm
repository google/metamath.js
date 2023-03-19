include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "cch.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "choccli.mm"
include "chincli.mm"
include "pjoml2i.mm"
include "chub1i.mm"
include "chdmm2i.mm"
include "sseqtr4i.mm"
include "jctil.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "sylancr.mm"

theorem pjoml6i
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH

  disjoint A x
  disjoint B x
  assert |- ( A C_ B -> E. x e. CH ( A C_ ( _|_ ` x ) /\ ( A vH x ) = B ) )

  proof
    cA
    cB
    wss
    #
    cA
    cort
    cfv
    #
    cB
    cin
    #
    cch
    wcel
    cA
    @2
    cort
    cfv
    #
    wss
    #
    cA
    @2
    chj
    co
    #
    cB
    wceq
    #
    wa
    #
    cA
    vx
    cv
    #
    cort
    cfv
    #
    wss
    #
    cA
    @8
    chj
    co
    #
    cB
    wceq
    #
    wa
    #
    vx
    cch
    wrex
    @1
    cB
    cA
    pjoml2.1
    choccli
    pjoml2.2
    chincli
    @0
    @6
    @4
    cA
    cB
    pjoml2.1
    pjoml2.2
    pjoml2i
    cA
    cA
    cB
    cort
    cfv
    #
    chj
    co
    @3
    cA
    @14
    pjoml2.1
    cB
    pjoml2.2
    choccli
    chub1i
    cA
    cB
    pjoml2.1
    pjoml2.2
    chdmm2i
    sseqtr4i
    jctil
    @13
    @7
    vx
    @2
    cch
    @8
    @2
    wceq
    #
    @10
    @4
    @12
    @6
    @15
    @9
    @3
    cA
    @8
    @2
    cort
    fveq2
    sseq2d
    @15
    @11
    @5
    cB
    @8
    @2
    cA
    chj
    oveq2
    eqeq1d
    anbi12d
    rspcev
    sylancr
end
