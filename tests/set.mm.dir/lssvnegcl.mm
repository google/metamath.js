include "clmod.mm"
include "wcel.mm"
include "w3a.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "cminusg.mm"
include "cvsca.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "eqid.mm"
include "lssel.mm"
include "lmodvneg1.mm"
include "sylan2.mm"
include "3impb.mm"
include "simp1.mm"
include "simp2.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "3ad2ant1.mm"
include "ringgrp.mm"
include "syl.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simp3.mm"
include "lssvscl.mm"
include "syl22anc.mm"
include "eqeltrrd.mm"

theorem lssvnegcl
  let cS: class S
  let cU: class U
  let cN: class N
  let cW: class W
  let cX: class X
  assume lssvnegcl.s: |- S = ( LSubSp ` W )
  assume lssvnegcl.n: |- N = ( invg ` W )


  assert |- ( ( W e. LMod /\ U e. S /\ X e. U ) -> ( N ` X ) e. U )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    cX
    cU
    wcel
    #
    w3a
    #
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @4
    cminusg
    cfv
    #
    cfv
    #
    cX
    cW
    cvsca
    cfv
    #
    co
    #
    cX
    cN
    cfv
    #
    cU
    @0
    @1
    @2
    @9
    @10
    wceq
    #
    @1
    @2
    wa
    @0
    cX
    cW
    cbs
    cfv
    #
    wcel
    @11
    cS
    cU
    @12
    cW
    cX
    @12
    eqid
    #
    lssvnegcl.s
    lssel
    @8
    @5
    @4
    @6
    cN
    @12
    cW
    cX
    @13
    lssvnegcl.n
    @4
    eqid
    #
    @8
    eqid
    #
    @5
    eqid
    #
    @6
    eqid
    #
    lmodvneg1
    sylan2
    3impb
    @3
    @0
    @1
    @7
    @4
    cbs
    cfv
    #
    wcel
    #
    @2
    @9
    cU
    wcel
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @3
    @4
    cgrp
    wcel
    #
    @5
    @18
    wcel
    #
    @19
    @3
    @4
    crg
    wcel
    #
    @20
    @0
    @1
    @22
    @2
    @4
    cW
    @14
    lmodring
    3ad2ant1
    #
    @4
    ringgrp
    syl
    @3
    @22
    @21
    @23
    @18
    @4
    @5
    @18
    eqid
    #
    @16
    ringidcl
    syl
    @18
    @4
    @6
    @5
    @24
    @17
    grpinvcl
    syl2anc
    @0
    @1
    @2
    simp3
    @18
    cS
    @8
    cU
    @4
    cW
    @7
    cX
    @14
    @15
    @24
    lssvnegcl.s
    lssvscl
    syl22anc
    eqeltrrd
end
