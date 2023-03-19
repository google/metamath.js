include "cofld.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "cfield.mm"
include "wa.mm"
include "corng.mm"
include "simpr.mm"
include "crg.mm"
include "isofld.mm"
include "simprbi.mm"
include "adantr.mm"
include "ccrg.mm"
include "cdr.mm"
include "isfld.mm"
include "crngring.mm"
include "3syl.mm"
include "suborng.mm"
include "syl2anc.mm"
include "sylanbrc.mm"

theorem subofld
  let cA: class A
  let cF: class F


  assert |- ( ( F e. oField /\ ( F |`s A ) e. Field ) -> ( F |`s A ) e. oField )

  proof
    cF
    cofld
    wcel
    #
    cF
    cA
    cress
    co
    #
    cfield
    wcel
    #
    wa
    #
    @2
    @1
    corng
    wcel
    #
    @1
    cofld
    wcel
    @0
    @2
    simpr
    #
    @3
    cF
    corng
    wcel
    #
    @1
    crg
    wcel
    #
    @4
    @0
    @6
    @2
    @0
    cF
    cfield
    wcel
    @6
    cF
    isofld
    simprbi
    adantr
    @3
    @2
    @1
    ccrg
    wcel
    #
    @7
    @5
    @2
    @1
    cdr
    wcel
    @8
    @1
    isfld
    simprbi
    @1
    crngring
    3syl
    cA
    cF
    suborng
    syl2anc
    @1
    isofld
    sylanbrc
end
