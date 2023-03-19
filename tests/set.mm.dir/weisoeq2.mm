include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "wiso.mm"
include "wceq.mm"
include "ccnv.mm"
include "isocnv.mm"
include "anim12i.mm"
include "weisoeq.mm"
include "sylan2.mm"
include "wrel.mm"
include "wb.mm"
include "wf1o.mm"
include "simprl.mm"
include "isof1o.mm"
include "f1orel.mm"
include "3syl.mm"
include "simprr.mm"
include "cnveqb.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem weisoeq2
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( ( S We B /\ S Se B ) /\ ( F Isom R , S ( A , B ) /\ G Isom R , S ( A , B ) ) ) -> F = G )

  proof
    cB
    cS
    wwe
    cB
    cS
    wse
    wa
    #
    cA
    cB
    cR
    cS
    cF
    wiso
    #
    cA
    cB
    cR
    cS
    cG
    wiso
    #
    wa
    #
    wa
    #
    cF
    cG
    wceq
    #
    cF
    ccnv
    #
    cG
    ccnv
    #
    wceq
    #
    @3
    @0
    cB
    cA
    cS
    cR
    @6
    wiso
    #
    cB
    cA
    cS
    cR
    @7
    wiso
    #
    wa
    @8
    @1
    @9
    @2
    @10
    cA
    cB
    cR
    cS
    cF
    isocnv
    cA
    cB
    cR
    cS
    cG
    isocnv
    anim12i
    cB
    cA
    cS
    cR
    @6
    @7
    weisoeq
    sylan2
    @4
    cF
    wrel
    #
    cG
    wrel
    #
    @5
    @8
    wb
    @4
    @1
    cA
    cB
    cF
    wf1o
    @11
    @0
    @1
    @2
    simprl
    cA
    cB
    cR
    cS
    cF
    isof1o
    cA
    cB
    cF
    f1orel
    3syl
    @4
    @2
    cA
    cB
    cG
    wf1o
    @12
    @0
    @1
    @2
    simprr
    cA
    cB
    cR
    cS
    cG
    isof1o
    cA
    cB
    cG
    f1orel
    3syl
    cF
    cG
    cnveqb
    syl2anc
    mpbird
end
