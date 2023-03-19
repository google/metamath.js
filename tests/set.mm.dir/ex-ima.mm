include "c2.mm"
include "c6.mm"
include "cop.mm"
include "c3.mm"
include "c9.mm"
include "cpr.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cima.mm"
include "csn.mm"
include "crn.mm"
include "cres.mm"
include "df-ima.mm"
include "ex-res.mm"
include "rneqd.mm"
include "syl5eq.mm"
include "2ex.mm"
include "rnsnop.mm"
include "syl6eq.mm"

theorem ex-ima
  let cB: class B
  let cF: class F


  assert |- ( ( F = { <. 2 , 6 >. , <. 3 , 9 >. } /\ B = { 1 , 2 } ) -> ( F " B ) = { 6 } )

  proof
    cF
    c2
    c6
    cop
    #
    c3
    c9
    cop
    cpr
    wceq
    cB
    c1
    c2
    cpr
    wceq
    wa
    #
    cF
    cB
    cima
    #
    @0
    csn
    #
    crn
    #
    c6
    csn
    @1
    @2
    cF
    cB
    cres
    #
    crn
    @4
    cF
    cB
    df-ima
    @1
    @5
    @3
    cB
    cF
    ex-res
    rneqd
    syl5eq
    c2
    c6
    2ex
    rnsnop
    syl6eq
end
