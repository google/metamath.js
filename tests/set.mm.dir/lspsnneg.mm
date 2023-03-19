include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "csn.mm"
include "csca.mm"
include "cur.mm"
include "cminusg.mm"
include "cvsca.mm"
include "co.mm"
include "eqid.mm"
include "lmodvneg1.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "cbs.mm"
include "wss.mm"
include "simpl.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "lmod1cl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simpr.mm"
include "lspsnvsi.mm"
include "syl3anc.mm"
include "eqsstr3d.mm"
include "wceq.mm"
include "lmodvnegcl.mm"
include "syldan.mm"
include "lmodgrp.mm"
include "grpinvinv.mm"
include "sylan.mm"
include "eqtrd.mm"
include "eqssd.mm"

theorem lspsnneg
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  assume lspsnneg.v: |- V = ( Base ` W )
  assume lspsnneg.m: |- M = ( invg ` W )
  assume lspsnneg.n: |- N = ( LSpan ` W )


  assert |- ( ( W e. LMod /\ X e. V ) -> ( N ` { ( M ` X ) } ) = ( N ` { X } ) )

  proof
    cW
    clmod
    wcel
    #
    cX
    cV
    wcel
    #
    wa
    #
    cX
    cM
    cfv
    #
    csn
    #
    cN
    cfv
    #
    cX
    csn
    #
    cN
    cfv
    #
    @2
    @5
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @8
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
    csn
    #
    cN
    cfv
    #
    @7
    @2
    @14
    @4
    cN
    @2
    @13
    @3
    @12
    @9
    @8
    @10
    cM
    cV
    cW
    cX
    lspsnneg.v
    lspsnneg.m
    @8
    eqid
    #
    @12
    eqid
    #
    @9
    eqid
    #
    @10
    eqid
    #
    lmodvneg1
    sneqd
    fveq2d
    @2
    @0
    @11
    @8
    cbs
    cfv
    #
    wcel
    #
    @1
    @15
    @7
    wss
    @0
    @1
    simpl
    #
    @0
    @21
    @1
    @0
    @8
    cgrp
    wcel
    @9
    @20
    wcel
    @21
    @8
    cW
    @16
    lmodfgrp
    @9
    @8
    @20
    cW
    @16
    @20
    eqid
    #
    @18
    lmod1cl
    @20
    @8
    @10
    @9
    @23
    @19
    grpinvcl
    syl2anc
    adantr
    #
    @0
    @1
    simpr
    @11
    @12
    @8
    @20
    cN
    cV
    cW
    cX
    @16
    @23
    lspsnneg.v
    @17
    lspsnneg.n
    lspsnvsi
    syl3anc
    eqsstr3d
    @2
    @7
    @11
    @3
    @12
    co
    #
    csn
    #
    cN
    cfv
    #
    @5
    @2
    @26
    @6
    cN
    @2
    @25
    cX
    @2
    @25
    @3
    cM
    cfv
    #
    cX
    @0
    @1
    @3
    cV
    wcel
    #
    @25
    @28
    wceq
    cM
    cV
    cW
    cX
    lspsnneg.v
    lspsnneg.m
    lmodvnegcl
    #
    @12
    @9
    @8
    @10
    cM
    cV
    cW
    @3
    lspsnneg.v
    lspsnneg.m
    @16
    @17
    @18
    @19
    lmodvneg1
    syldan
    @0
    cW
    cgrp
    wcel
    @1
    @28
    cX
    wceq
    cW
    lmodgrp
    cV
    cW
    cM
    cX
    lspsnneg.v
    lspsnneg.m
    grpinvinv
    sylan
    eqtrd
    sneqd
    fveq2d
    @2
    @0
    @21
    @29
    @27
    @5
    wss
    @22
    @24
    @30
    @11
    @12
    @8
    @20
    cN
    cV
    cW
    @3
    @16
    @23
    lspsnneg.v
    @17
    lspsnneg.n
    lspsnvsi
    syl3anc
    eqsstr3d
    eqssd
end
