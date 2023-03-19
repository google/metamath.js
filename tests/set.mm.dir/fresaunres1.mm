include "wf.mm"
include "cin.mm"
include "cres.mm"
include "wceq.mm"
include "w3a.mm"
include "cun.mm"
include "uncom.mm"
include "reseq1i.mm"
include "incom.mm"
include "reseq2i.mm"
include "eqeq12i.mm"
include "eqcom.mm"
include "bitri.mm"
include "fresaunres2.mm"
include "3com12.mm"
include "syl3an3b.mm"
include "syl5eq.mm"

theorem fresaunres1
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G


  assert |- ( ( F : A --> C /\ G : B --> C /\ ( F |` ( A i^i B ) ) = ( G |` ( A i^i B ) ) ) -> ( ( F u. G ) |` A ) = F )

  proof
    cA
    cC
    cF
    wf
    #
    cB
    cC
    cG
    wf
    #
    cF
    cA
    cB
    cin
    #
    cres
    #
    cG
    @2
    cres
    #
    wceq
    #
    w3a
    cF
    cG
    cun
    #
    cA
    cres
    cG
    cF
    cun
    #
    cA
    cres
    #
    cF
    @6
    @7
    cA
    cF
    cG
    uncom
    reseq1i
    @5
    @0
    @1
    cG
    cB
    cA
    cin
    #
    cres
    #
    cF
    @9
    cres
    #
    wceq
    #
    @8
    cF
    wceq
    #
    @5
    @11
    @10
    wceq
    @12
    @3
    @11
    @4
    @10
    @2
    @9
    cF
    cA
    cB
    incom
    #
    reseq2i
    @2
    @9
    cG
    @14
    reseq2i
    eqeq12i
    @11
    @10
    eqcom
    bitri
    @1
    @0
    @12
    @13
    cB
    cA
    cC
    cG
    cF
    fresaunres2
    3com12
    syl3an3b
    syl5eq
end
