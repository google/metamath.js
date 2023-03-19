include "c2o.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "wf.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "cixp.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "ifid.mm"
include "eleq2i.mm"
include "ralbii.mm"
include "anbi2i.mm"
include "ovex.mm"
include "cnvex.mm"
include "elixp.mm"
include "ffnfv.mm"
include "3bitr4i.mm"
include "xpsfrnel2.mm"
include "bitr3i.mm"

theorem xpscf
  let cA: class A
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let cB: class B
  let cG: class G


  assert |- ( `' ( { X } +c { Y } ) : 2o --> A <-> ( X e. A /\ Y e. A ) )

  proof
    c2o
    cA
    cX
    csn
    #
    cY
    csn
    #
    ccda
    co
    #
    ccnv
    #
    wf
    #
    @3
    vk
    c2o
    vk
    cv
    #
    c0
    wceq
    #
    cA
    cA
    cif
    #
    cixp
    wcel
    #
    cX
    cA
    wcel
    cY
    cA
    wcel
    wa
    @3
    c2o
    wfn
    #
    @5
    @3
    cfv
    #
    @7
    wcel
    #
    vk
    c2o
    wral
    #
    wa
    @9
    @10
    cA
    wcel
    #
    vk
    c2o
    wral
    #
    wa
    @8
    @4
    @12
    @14
    @9
    @11
    @13
    vk
    c2o
    @7
    cA
    @10
    @6
    cA
    ifid
    eleq2i
    ralbii
    anbi2i
    vk
    c2o
    @7
    @3
    @2
    @0
    @1
    ccda
    ovex
    cnvex
    elixp
    vk
    c2o
    cA
    @3
    ffnfv
    3bitr4i
    cA
    cA
    vk
    cX
    cY
    xpsfrnel2
    bitr3i
end
