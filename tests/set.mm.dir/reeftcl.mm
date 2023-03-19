include "cr.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cfa.mm"
include "cfv.mm"
include "reexpcl.mm"
include "cn.mm"
include "faccl.mm"
include "adantl.mm"
include "nndivred.mm"

theorem reeftcl
  let cA: class A
  let cK: class K


  assert |- ( ( A e. RR /\ K e. NN0 ) -> ( ( A ^ K ) / ( ! ` K ) ) e. RR )

  proof
    cA
    cr
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
    reexpcl
    @1
    @2
    cn
    wcel
    @0
    cK
    faccl
    adantl
    nndivred
end
