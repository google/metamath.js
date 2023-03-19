include "crelexp.mm"
include "co.mm"
include "cdm.mm"
include "crn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "ccom.mm"
include "wcel.mm"
include "wrel.mm"
include "wa.mm"
include "cn0.mm"
include "caddc.mm"
include "coeq0.mm"
include "c1.mm"
include "wi.mm"
include "simprl.mm"
include "simprr.mm"
include "simpll.mm"
include "simplr.mm"
include "a1d.mm"
include "relexpaddg.mm"
include "syl13anc.mm"
include "eqeq1d.mm"
include "syl5bbr.mm"

theorem relexpnul
  let cR: class R
  let cM: class M
  let cN: class N
  let cV: class V


  assert |- ( ( ( R e. V /\ Rel R ) /\ ( N e. NN0 /\ M e. NN0 ) ) -> ( ( dom ( R ^r N ) i^i ran ( R ^r M ) ) = (/) <-> ( R ^r ( N + M ) ) = (/) ) )

  proof
    cR
    cN
    crelexp
    co
    #
    cdm
    cR
    cM
    crelexp
    co
    #
    crn
    cin
    c0
    wceq
    @0
    @1
    ccom
    #
    c0
    wceq
    cR
    cV
    wcel
    #
    cR
    wrel
    #
    wa
    #
    cN
    cn0
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    wa
    #
    cR
    cN
    cM
    caddc
    co
    #
    crelexp
    co
    #
    c0
    wceq
    @0
    @1
    coeq0
    @9
    @2
    @11
    c0
    @9
    @6
    @7
    @3
    @10
    c1
    wceq
    #
    @4
    wi
    @2
    @11
    wceq
    @5
    @6
    @7
    simprl
    @5
    @6
    @7
    simprr
    @3
    @4
    @8
    simpll
    @9
    @4
    @12
    @3
    @4
    @8
    simplr
    a1d
    cR
    cM
    cN
    cV
    relexpaddg
    syl13anc
    eqeq1d
    syl5bbr
end
