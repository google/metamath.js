include "wf1o.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wreu.mm"
include "cop.mm"
include "ccnv.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "syl.mm"
include "feu.mm"
include "sylan.mm"
include "wb.mm"
include "w3a.mm"
include "f1ocnvfvb.mm"
include "3com23.mm"
include "wfn.mm"
include "dff1o4.mm"
include "simprbi.mm"
include "fnopfvb.mm"
include "3adant3.mm"
include "syl3an1.mm"
include "bitrd.mm"
include "3expa.mm"
include "reubidva.mm"
include "mpbird.mm"

theorem f1ofveu
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F

  disjoint A x
  disjoint B x
  disjoint C x
  disjoint F x
  assert |- ( ( F : A -1-1-onto-> B /\ C e. B ) -> E! x e. A ( F ` x ) = C )

  proof
    cA
    cB
    cF
    wf1o
    #
    cC
    cB
    wcel
    #
    wa
    #
    vx
    cv
    #
    cF
    cfv
    cC
    wceq
    #
    vx
    cA
    wreu
    cC
    @3
    cop
    cF
    ccnv
    #
    wcel
    #
    vx
    cA
    wreu
    #
    @0
    cB
    cA
    @5
    wf
    #
    @1
    @7
    @0
    cB
    cA
    @5
    wf1o
    @8
    cA
    cB
    cF
    f1ocnv
    cB
    cA
    @5
    f1of
    syl
    vx
    cB
    cA
    cC
    @5
    feu
    sylan
    @2
    @4
    @6
    vx
    cA
    @0
    @1
    @3
    cA
    wcel
    #
    @4
    @6
    wb
    @0
    @1
    @9
    w3a
    @4
    cC
    @5
    cfv
    @3
    wceq
    #
    @6
    @0
    @9
    @1
    @4
    @10
    wb
    cA
    cB
    @3
    cC
    cF
    f1ocnvfvb
    3com23
    @0
    @5
    cB
    wfn
    #
    @1
    @9
    @10
    @6
    wb
    #
    @0
    cF
    cA
    wfn
    @11
    cA
    cB
    cF
    dff1o4
    simprbi
    @11
    @1
    @12
    @9
    cB
    cC
    @3
    @5
    fnopfvb
    3adant3
    syl3an1
    bitrd
    3expa
    reubidva
    mpbird
end
