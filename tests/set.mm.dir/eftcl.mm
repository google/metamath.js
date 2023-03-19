include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "expcl.mm"
include "faccl.mm"
include "nncnd.mm"
include "adantl.mm"
include "cc0.mm"
include "wne.mm"
include "facne0.mm"
include "divcld.mm"

theorem eftcl
  let cA: class A
  let cK: class K


  assert |- ( ( A e. CC /\ K e. NN0 ) -> ( ( A ^ K ) / ( ! ` K ) ) e. CC )

  proof
    cA
    cc
    wcel
    #
    cK
    cn0
    wcel
    #
    wa
    cA
    cK
    cexp
    co
    cK
    cfa
    cfv
    #
    cA
    cK
    expcl
    @1
    @2
    cc
    wcel
    @0
    @1
    @2
    cK
    faccl
    nncnd
    adantl
    @1
    @2
    cc0
    wne
    @0
    cK
    facne0
    adantl
    divcld
end
