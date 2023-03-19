include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "wa.mm"
include "cpjh.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "chel.mm"
include "jca.mm"
include "pjch.mm"
include "biimpa.mm"
include "sylancom.mm"

theorem pjid
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. H ) -> ( ( projh ` H ) ` A ) = A )

  proof
    cH
    cch
    wcel
    #
    cA
    cH
    wcel
    #
    @0
    cA
    chil
    wcel
    #
    wa
    #
    cA
    cH
    cpjh
    cfv
    cfv
    cA
    wceq
    #
    @0
    @1
    wa
    @0
    @2
    @0
    @1
    simpl
    cA
    cH
    chel
    jca
    @3
    @1
    @4
    cA
    cH
    pjch
    biimpa
    sylancom
end
