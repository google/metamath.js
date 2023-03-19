include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cmpt.mm"
include "cpw.mm"
include "ccn.mm"
include "co.mm"
include "ccncf.mm"
include "cnfdmsn.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "crest.mm"
include "wss.mm"
include "wceq.mm"
include "snssi.mm"
include "eqid.mm"
include "cncfcn.mm"
include "syl2an.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "simpl.mm"
include "restsn2.mm"
include "sylancr.mm"
include "simpr.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "eleqtrd.mm"

theorem cncfdmsn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint A x
  disjoint B x
  disjoint k x
  assert |- ( ( A e. CC /\ B e. CC ) -> ( x e. { A } |-> B ) e. ( { A } -cn-> { B } ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    vx
    cA
    csn
    #
    cB
    cmpt
    @3
    cpw
    #
    cB
    csn
    #
    cpw
    #
    ccn
    co
    #
    @3
    @5
    ccncf
    co
    #
    vx
    cA
    cB
    cc
    cc
    cnfdmsn
    @2
    @8
    ccnfld
    ctopn
    cfv
    #
    @3
    crest
    co
    #
    @9
    @5
    crest
    co
    #
    ccn
    co
    #
    @7
    @0
    @3
    cc
    wss
    @5
    cc
    wss
    @8
    @12
    wceq
    @1
    cA
    cc
    snssi
    cB
    cc
    snssi
    @3
    @5
    @9
    @10
    @11
    @9
    eqid
    #
    @10
    eqid
    @11
    eqid
    cncfcn
    syl2an
    @2
    @10
    @4
    @11
    @6
    ccn
    @2
    @9
    cc
    ctopon
    cfv
    wcel
    #
    @0
    @10
    @4
    wceq
    @9
    @13
    cnfldtopon
    #
    @0
    @1
    simpl
    cA
    @9
    cc
    restsn2
    sylancr
    @2
    @14
    @1
    @11
    @6
    wceq
    @15
    @0
    @1
    simpr
    cB
    @9
    cc
    restsn2
    sylancr
    oveq12d
    eqtr2d
    eleqtrd
end
