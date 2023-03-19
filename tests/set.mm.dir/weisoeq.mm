include "wwe.mm"
include "wse.mm"
include "wa.mm"
include "wiso.mm"
include "wceq.mm"
include "ccnv.mm"
include "ccom.mm"
include "cid.mm"
include "cres.mm"
include "id.mm"
include "isocnv.mm"
include "isotr.mm"
include "syl2anr.mm"
include "weniso.mm"
include "3expa.mm"
include "sylan2.mm"
include "wf1.mm"
include "wb.mm"
include "wf1o.mm"
include "simprl.mm"
include "isof1o.mm"
include "f1of1.mm"
include "3syl.mm"
include "simprr.mm"
include "f1eqcocnv.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem weisoeq
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vc: setvar c


  assert |- ( ( ( R We A /\ R Se A ) /\ ( F Isom R , S ( A , B ) /\ G Isom R , S ( A , B ) ) ) -> F = G )

  proof
    cA
    cR
    wwe
    #
    cA
    cR
    wse
    #
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
    ccom
    #
    cid
    cA
    cres
    wceq
    #
    @5
    @2
    cA
    cA
    cR
    cR
    @9
    wiso
    #
    @10
    @4
    @4
    cB
    cA
    cS
    cR
    @8
    wiso
    @11
    @3
    @4
    id
    cA
    cB
    cR
    cS
    cF
    isocnv
    cA
    cB
    cA
    cR
    cS
    cR
    @8
    cG
    isotr
    syl2anr
    @0
    @1
    @11
    @10
    cA
    cR
    @9
    weniso
    3expa
    sylan2
    @6
    cA
    cB
    cF
    wf1
    #
    cA
    cB
    cG
    wf1
    #
    @7
    @10
    wb
    @6
    @3
    cA
    cB
    cF
    wf1o
    @12
    @2
    @3
    @4
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
    f1of1
    3syl
    @6
    @4
    cA
    cB
    cG
    wf1o
    @13
    @2
    @3
    @4
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
    f1of1
    3syl
    cA
    cB
    cF
    cG
    f1eqcocnv
    syl2anc
    mpbird
end
