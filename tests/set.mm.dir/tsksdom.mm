include "ctsk.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "canth2g.mm"
include "adantl.mm"
include "wss.mm"
include "simpl.mm"
include "tskpwss.mm"
include "ssdomg.mm"
include "sylc.mm"
include "sdomdomtr.mm"
include "syl2anc.mm"

theorem tsksdom
  let cA: class A
  let cT: class T


  assert |- ( ( T e. Tarski /\ A e. T ) -> A ~< T )

  proof
    cT
    ctsk
    wcel
    #
    cA
    cT
    wcel
    #
    wa
    #
    cA
    cA
    cpw
    #
    csdm
    wbr
    #
    @3
    cT
    cdom
    wbr
    #
    cA
    cT
    csdm
    wbr
    @1
    @4
    @0
    cA
    cT
    canth2g
    adantl
    @2
    @0
    @3
    cT
    wss
    @5
    @0
    @1
    simpl
    cA
    cT
    tskpwss
    @3
    cT
    ctsk
    ssdomg
    sylc
    cA
    @3
    cT
    sdomdomtr
    syl2anc
end
