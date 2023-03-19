include "wf1.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cima.mm"
include "cvv.mm"
include "cres.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "simprr.mm"
include "simplr.mm"
include "wf.mm"
include "f1f.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "syl.mm"
include "ad2antrr.mm"
include "ssexd.mm"
include "f1ores.mm"
include "ad2ant2r.mm"
include "f1oen2g.mm"
include "syl3anc.mm"
include "ensymd.mm"

theorem f1imaen2g
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V


  assert |- ( ( ( F : A -1-1-> B /\ B e. V ) /\ ( C C_ A /\ C e. V ) ) -> ( F " C ) ~~ C )

  proof
    cA
    cB
    cF
    wf1
    #
    cB
    cV
    wcel
    #
    wa
    #
    cC
    cA
    wss
    #
    cC
    cV
    wcel
    #
    wa
    #
    wa
    #
    cC
    cF
    cC
    cima
    #
    @6
    @4
    @7
    cvv
    wcel
    cC
    @7
    cF
    cC
    cres
    #
    wf1o
    #
    cC
    @7
    cen
    wbr
    @2
    @3
    @4
    simprr
    @6
    @7
    cB
    cV
    @0
    @1
    @5
    simplr
    @0
    @7
    cB
    wss
    #
    @1
    @5
    @0
    cA
    cB
    cF
    wf
    #
    @10
    cA
    cB
    cF
    f1f
    @11
    @7
    cF
    crn
    cB
    cF
    cC
    imassrn
    cA
    cB
    cF
    frn
    syl5ss
    syl
    ad2antrr
    ssexd
    @0
    @3
    @9
    @1
    @4
    cA
    cB
    cC
    cF
    f1ores
    ad2ant2r
    cC
    @7
    @8
    cV
    cvv
    f1oen2g
    syl3anc
    ensymd
end
