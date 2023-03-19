include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cs2.mm"
include "ccnv.mm"
include "wfun.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "cvv.mm"
include "c0ex.mm"
include "1ex.mm"
include "simp3.mm"
include "funcnvpr.mm"
include "mp3an12i.mm"
include "wceq.mm"
include "s2prop.mm"
include "3adant3.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "mpbird.mm"

theorem funcnvs2
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. V /\ B e. V /\ A =/= B ) -> Fun `' <" A B "> )

  proof
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cA
    cB
    cs2
    #
    ccnv
    #
    wfun
    cc0
    cA
    cop
    c1
    cB
    cop
    cpr
    #
    ccnv
    #
    wfun
    #
    cc0
    cvv
    wcel
    c1
    cvv
    wcel
    @3
    @2
    @8
    c0ex
    1ex
    @0
    @1
    @2
    simp3
    cc0
    cA
    c1
    cB
    cvv
    cvv
    funcnvpr
    mp3an12i
    @3
    @5
    @7
    @3
    @4
    @6
    @0
    @1
    @4
    @6
    wceq
    @2
    cA
    cB
    cV
    s2prop
    3adant3
    cnveqd
    funeqd
    mpbird
end
