include "chmph.mm"
include "wbr.mm"
include "wcel.mm"
include "wi.mm"
include "hmphsym.mm"
include "chmeo.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "hmph.mm"
include "cv.mm"
include "wex.mm"
include "n0.mm"
include "wa.mm"
include "cuni.mm"
include "wf1.mm"
include "ccn.mm"
include "simpl.mm"
include "wf1o.mm"
include "eqid.mm"
include "hmeof1o.mm"
include "adantl.mm"
include "f1of1.mm"
include "syl.mm"
include "hmeocn.mm"
include "syl3anc.mm"
include "expcom.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem haushmphlem
  let cA: class A
  let vf: setvar f
  let cJ: class J
  let cK: class K
  assume haushmphlem.1: |- ( J e. A -> J e. Top )
  assume haushmphlem.2: |- ( ( J e. A /\ f : U. K -1-1-> U. J /\ f e. ( K Cn J ) ) -> K e. A )

  disjoint A f
  disjoint J f
  disjoint K f
  assert |- ( J ~= K -> ( J e. A -> K e. A ) )

  proof
    cJ
    cK
    chmph
    wbr
    cK
    cJ
    chmph
    wbr
    #
    cJ
    cA
    wcel
    #
    cK
    cA
    wcel
    #
    wi
    #
    cJ
    cK
    hmphsym
    @0
    cK
    cJ
    chmeo
    co
    #
    c0
    wne
    #
    @3
    cK
    cJ
    hmph
    @5
    vf
    cv
    #
    @4
    wcel
    #
    vf
    wex
    @3
    vf
    @4
    n0
    @7
    @3
    vf
    @1
    @7
    @2
    @1
    @7
    wa
    #
    @1
    cK
    cuni
    #
    cJ
    cuni
    #
    @6
    wf1
    #
    @6
    cK
    cJ
    ccn
    co
    wcel
    #
    @2
    @1
    @7
    simpl
    @8
    @9
    @10
    @6
    wf1o
    #
    @11
    @7
    @13
    @1
    @6
    cK
    cJ
    @9
    @10
    @9
    eqid
    @10
    eqid
    hmeof1o
    adantl
    @9
    @10
    @6
    f1of1
    syl
    @7
    @12
    @1
    @6
    cK
    cJ
    hmeocn
    adantl
    haushmphlem.2
    syl3anc
    expcom
    exlimiv
    sylbi
    sylbi
    syl
end
