include "ccrg.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "ce1.mm"
include "cfv.mm"
include "crn.mm"
include "cv1.mm"
include "eqid.mm"
include "evl1var.mm"
include "cpl1.mm"
include "cbs.mm"
include "wfn.mm"
include "cpws.mm"
include "co.mm"
include "crh.mm"
include "wf.mm"
include "evl1rhm.mm"
include "rhmf.mm"
include "ffn.mm"
include "3syl.mm"
include "crg.mm"
include "crngring.mm"
include "vr1cl.mm"
include "syl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "syl6eleqr.mm"

theorem pf1id
  let cB: class B
  let cQ: class Q
  let cR: class R
  assume pf1const.b: |- B = ( Base ` R )
  assume pf1const.q: |- Q = ran ( eval1 ` R )


  assert |- ( R e. CRing -> ( _I |` B ) e. Q )

  proof
    cR
    ccrg
    wcel
    #
    cid
    cB
    cres
    #
    cR
    ce1
    cfv
    #
    crn
    #
    cQ
    @0
    cR
    cv1
    cfv
    #
    @2
    cfv
    #
    @1
    @3
    cB
    cR
    @2
    @4
    @2
    eqid
    #
    @4
    eqid
    #
    pf1const.b
    evl1var
    @0
    @2
    cR
    cpl1
    cfv
    #
    cbs
    cfv
    #
    wfn
    #
    @4
    @9
    wcel
    #
    @5
    @3
    wcel
    @0
    @2
    @8
    cR
    cB
    cpws
    co
    #
    crh
    co
    wcel
    @9
    @12
    cbs
    cfv
    #
    @2
    wf
    @10
    cB
    @8
    cR
    @12
    @2
    @6
    @8
    eqid
    #
    @12
    eqid
    pf1const.b
    evl1rhm
    @9
    @13
    @8
    @12
    @2
    @9
    eqid
    #
    @13
    eqid
    rhmf
    @9
    @13
    @2
    ffn
    3syl
    @0
    cR
    crg
    wcel
    @11
    cR
    crngring
    @9
    @8
    cR
    @4
    @7
    @14
    @15
    vr1cl
    syl
    @9
    @4
    @2
    fnfvelrn
    syl2anc
    eqeltrrd
    pf1const.q
    syl6eleqr
end
