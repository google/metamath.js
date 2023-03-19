include "wcel.mm"
include "w3a.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cima.mm"
include "wss.mm"
include "cop.mm"
include "sneq.mm"
include "eqimss.mm"
include "syl.mm"
include "fvex.mm"
include "snsssn.mm"
include "impbii.mm"
include "wfn.mm"
include "elmapfn.mm"
include "simpl1.mm"
include "snidg.mm"
include "fnsnfv.mm"
include "syl2an2.mm"
include "sseq1d.mm"
include "syl5bb.mm"
include "pm5.32da.mm"
include "cvv.mm"
include "wb.mm"
include "snex.mm"
include "simp2.mm"
include "simp3.mm"
include "snssd.mm"
include "k0004lem2.mm"
include "mp3an2i.mm"
include "wf.mm"
include "elmap.mm"
include "fsng.mm"
include "3adant2.mm"
include "3bitrd.mm"

theorem k0004lem3
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cV: class V


  assert |- ( ( A e. U /\ B e. V /\ C e. B ) -> ( ( F e. ( B ^m { A } ) /\ ( F ` A ) = C ) <-> F = { <. A , C >. } ) )

  proof
    cA
    cU
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cB
    wcel
    #
    w3a
    #
    cF
    cB
    cA
    csn
    #
    cmap
    co
    wcel
    #
    cA
    cF
    cfv
    #
    cC
    wceq
    #
    wa
    @5
    cF
    @4
    cima
    #
    cC
    csn
    #
    wss
    #
    wa
    #
    cF
    @9
    @4
    cmap
    co
    wcel
    #
    cF
    cA
    cC
    cop
    csn
    wceq
    #
    @3
    @5
    @7
    @10
    @7
    @6
    csn
    #
    @9
    wss
    #
    @3
    @5
    wa
    #
    @10
    @7
    @15
    @7
    @14
    @9
    wceq
    @15
    @6
    cC
    sneq
    @14
    @9
    eqimss
    syl
    @6
    cC
    cA
    cF
    fvex
    snsssn
    impbii
    @16
    @14
    @8
    @9
    @5
    cF
    @4
    wfn
    @3
    cA
    @4
    wcel
    #
    @14
    @8
    wceq
    cF
    cB
    @4
    elmapfn
    @16
    @0
    @17
    @0
    @1
    @2
    @5
    simpl1
    cA
    cU
    snidg
    syl
    @4
    cA
    cF
    fnsnfv
    syl2an2
    sseq1d
    syl5bb
    pm5.32da
    @4
    cvv
    wcel
    @3
    @1
    @9
    cB
    wss
    @11
    @12
    wb
    cA
    snex
    #
    @0
    @1
    @2
    simp2
    @3
    cC
    cB
    @0
    @1
    @2
    simp3
    snssd
    @4
    cB
    @9
    cvv
    cF
    cV
    k0004lem2
    mp3an2i
    @12
    @4
    @9
    cF
    wf
    #
    @3
    @13
    @9
    @4
    cF
    cC
    snex
    @18
    elmap
    @0
    @2
    @19
    @13
    wb
    @1
    cA
    cC
    cU
    cB
    cF
    fsng
    3adant2
    syl5bb
    3bitrd
end
