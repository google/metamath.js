include "wss.mm"
include "cc.mm"
include "wa.mm"
include "ccncf.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "cncfss.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "ccn.mm"
include "ctopon.mm"
include "wcel.mm"
include "eqid.mm"
include "cnfldtopon.mm"
include "sstr.mm"
include "resttopon.mm"
include "sylancr.mm"
include "cnmptid.mm"
include "wceq.mm"
include "cncfcn.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "sseldd.mm"

theorem cncfmptid
  let vx: setvar x
  let cS: class S
  let cT: class T
  let cA: class A

  disjoint S x
  disjoint T x
  disjoint A x
  assert |- ( ( S C_ T /\ T C_ CC ) -> ( x e. S |-> x ) e. ( S -cn-> T ) )

  proof
    cS
    cT
    wss
    cT
    cc
    wss
    wa
    #
    cS
    cS
    ccncf
    co
    #
    cS
    cT
    ccncf
    co
    vx
    cS
    vx
    cv
    cmpt
    #
    cS
    cS
    cT
    cncfss
    @0
    @2
    ccnfld
    ctopn
    cfv
    #
    cS
    crest
    co
    #
    @4
    ccn
    co
    #
    @1
    @0
    vx
    @4
    cS
    @0
    @3
    cc
    ctopon
    cfv
    wcel
    cS
    cc
    wss
    #
    @4
    cS
    ctopon
    cfv
    wcel
    @3
    @3
    eqid
    #
    cnfldtopon
    cS
    cT
    cc
    sstr
    #
    cS
    @3
    cc
    resttopon
    sylancr
    cnmptid
    @0
    @6
    @6
    @1
    @5
    wceq
    @8
    @8
    cS
    cS
    @3
    @4
    @4
    @7
    @4
    eqid
    #
    @9
    cncfcn
    syl2anc
    eleqtrrd
    sseldd
end
