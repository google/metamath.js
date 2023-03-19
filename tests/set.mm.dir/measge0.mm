include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "measvxrge0.mm"
include "elxrge0.mm"
include "sylib.mm"
include "simprd.mm"

theorem measge0
  let cA: class A
  let cS: class S
  let cM: class M


  assert |- ( ( M e. ( measures ` S ) /\ A e. S ) -> 0 <_ ( M ` A ) )

  proof
    cM
    cS
    cmeas
    cfv
    wcel
    cA
    cS
    wcel
    wa
    #
    cA
    cM
    cfv
    #
    cxr
    wcel
    #
    cc0
    @1
    cle
    wbr
    #
    @0
    @1
    cc0
    cpnf
    cicc
    co
    wcel
    @2
    @3
    wa
    cA
    cS
    cM
    measvxrge0
    @1
    elxrge0
    sylib
    simprd
end
