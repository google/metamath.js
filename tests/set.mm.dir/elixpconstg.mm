include "wcel.mm"
include "cixp.mm"
include "wf.mm"
include "wi.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "cvv.mm"
include "elixp2.mm"
include "simp2bi.mm"
include "simp3bi.mm"
include "jca.mm"
include "ffnfv.mm"
include "sylibr.mm"
include "a1i.mm"
include "w3a.mm"
include "elex.mm"
include "adantr.mm"
include "ffn.mm"
include "adantl.mm"
include "simprbi.mm"
include "3jca.mm"
include "ex.mm"
include "impbid.mm"

theorem elixpconstg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V

  disjoint A x
  disjoint B x
  disjoint F x
  assert |- ( F e. V -> ( F e. X_ x e. A B <-> F : A --> B ) )

  proof
    cF
    cV
    wcel
    #
    cF
    vx
    cA
    cB
    cixp
    wcel
    #
    cA
    cB
    cF
    wf
    #
    @1
    @2
    wi
    @0
    @1
    cF
    cA
    wfn
    #
    vx
    cv
    cF
    cfv
    cB
    wcel
    vx
    cA
    wral
    #
    wa
    @2
    @1
    @3
    @4
    @1
    cF
    cvv
    wcel
    #
    @3
    @4
    vx
    cA
    cB
    cF
    elixp2
    #
    simp2bi
    @1
    @5
    @3
    @4
    @6
    simp3bi
    jca
    vx
    cA
    cB
    cF
    ffnfv
    #
    sylibr
    a1i
    @0
    @2
    @1
    @0
    @2
    wa
    #
    @5
    @3
    @4
    w3a
    @1
    @8
    @5
    @3
    @4
    @0
    @5
    @2
    cF
    cV
    elex
    adantr
    @2
    @3
    @0
    cA
    cB
    cF
    ffn
    adantl
    @2
    @4
    @0
    @2
    @3
    @4
    @7
    simprbi
    adantl
    3jca
    @6
    sylibr
    ex
    impbid
end
