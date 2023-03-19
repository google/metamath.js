include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "cmnf.mm"
include "wne.mm"
include "cpnf.mm"
include "wa.mm"
include "renemnf.mm"
include "adantl.mm"
include "renepnf.mm"
include "jca.mm"
include "ex.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "xrred.mm"
include "impbid.mm"

theorem xrre4
  let cA: class A


  assert |- ( A e. RR* -> ( A e. RR <-> ( A =/= -oo /\ A =/= +oo ) ) )

  proof
    cA
    cxr
    wcel
    #
    cA
    cr
    wcel
    #
    cA
    cmnf
    wne
    #
    cA
    cpnf
    wne
    #
    wa
    #
    @0
    @1
    @4
    @0
    @1
    wa
    @2
    @3
    @1
    @2
    @0
    cA
    renemnf
    adantl
    @1
    @3
    @0
    cA
    renepnf
    adantl
    jca
    ex
    @0
    @4
    @1
    @0
    @4
    wa
    cA
    @0
    @4
    simpl
    @0
    @2
    @3
    simprl
    @0
    @2
    @3
    simprr
    xrred
    ex
    impbid
end
