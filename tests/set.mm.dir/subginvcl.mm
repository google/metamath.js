include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cress.mm"
include "co.mm"
include "cminusg.mm"
include "cbs.mm"
include "cgrp.mm"
include "eqid.mm"
include "subggrp.mm"
include "adantr.mm"
include "simpr.mm"
include "wceq.mm"
include "subgbas.mm"
include "eleqtrd.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "subginv.mm"
include "3eltr4d.mm"

theorem subginvcl
  let cS: class S
  let cG: class G
  let cI: class I
  let cX: class X
  assume subginvcl.i: |- I = ( invg ` G )


  assert |- ( ( S e. ( SubGrp ` G ) /\ X e. S ) -> ( I ` X ) e. S )

  proof
    cS
    cG
    csubg
    cfv
    wcel
    #
    cX
    cS
    wcel
    #
    wa
    #
    cX
    cG
    cS
    cress
    co
    #
    cminusg
    cfv
    #
    cfv
    #
    @3
    cbs
    cfv
    #
    cX
    cI
    cfv
    cS
    @2
    @3
    cgrp
    wcel
    #
    cX
    @6
    wcel
    @5
    @6
    wcel
    @0
    @7
    @1
    cS
    cG
    @3
    @3
    eqid
    #
    subggrp
    adantr
    @2
    cX
    cS
    @6
    @0
    @1
    simpr
    @0
    cS
    @6
    wceq
    @1
    cS
    cG
    @3
    @8
    subgbas
    adantr
    #
    eleqtrd
    @6
    @3
    @4
    cX
    @6
    eqid
    @4
    eqid
    #
    grpinvcl
    syl2anc
    cS
    cG
    @3
    cI
    @4
    cX
    @8
    subginvcl.i
    @10
    subginv
    @9
    3eltr4d
end
