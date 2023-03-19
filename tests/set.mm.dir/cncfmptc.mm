include "wcel.mm"
include "cc.mm"
include "wss.mm"
include "w3a.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "co.mm"
include "ccn.mm"
include "ccncf.mm"
include "ctopon.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "simp2.mm"
include "resttopon.mm"
include "sylancr.mm"
include "simp3.mm"
include "simp1.mm"
include "cnmptc.mm"
include "wceq.mm"
include "cncfcn.mm"
include "3adant1.mm"
include "eleqtrrd.mm"

theorem cncfmptc
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cT: class T

  disjoint A x
  disjoint S x
  disjoint T x
  assert |- ( ( A e. T /\ S C_ CC /\ T C_ CC ) -> ( x e. S |-> A ) e. ( S -cn-> T ) )

  proof
    cA
    cT
    wcel
    #
    cS
    cc
    wss
    #
    cT
    cc
    wss
    #
    w3a
    #
    vx
    cS
    cA
    cmpt
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    @4
    cT
    crest
    co
    #
    ccn
    co
    #
    cS
    cT
    ccncf
    co
    #
    @3
    vx
    cA
    @5
    @6
    cS
    cT
    @3
    @4
    cc
    ctopon
    cfv
    wcel
    #
    @1
    @5
    cS
    ctopon
    cfv
    wcel
    @4
    @4
    eqid
    #
    cnfldtopon
    #
    @0
    @1
    @2
    simp2
    cS
    @4
    cc
    resttopon
    sylancr
    @3
    @9
    @2
    @6
    cT
    ctopon
    cfv
    wcel
    @11
    @0
    @1
    @2
    simp3
    cT
    @4
    cc
    resttopon
    sylancr
    @0
    @1
    @2
    simp1
    cnmptc
    @1
    @2
    @8
    @7
    wceq
    @0
    cS
    cT
    @4
    @5
    @6
    @10
    @5
    eqid
    @6
    eqid
    cncfcn
    3adant1
    eleqtrrd
end
