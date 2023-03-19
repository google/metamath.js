include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cur.mm"
include "cdsr.mm"
include "wbr.mm"
include "coppr.mm"
include "simpl.mm"
include "cbs.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "eqid.mm"
include "unitcl.mm"
include "grpinvcl.mm"
include "syl2an.mm"
include "dvdsrneg.mm"
include "syldan.mm"
include "wceq.mm"
include "grpinvinv.mm"
include "breqtrd.mm"
include "simpr.mm"
include "isunit.mm"
include "sylib.mm"
include "simpld.mm"
include "dvdsrtr.mm"
include "syl3anc.mm"
include "opprring.mm"
include "adantr.mm"
include "opprbas.mm"
include "opprneg.mm"
include "syl2anc.mm"
include "simprd.mm"
include "sylanbrc.mm"

theorem unitnegcl
  let cR: class R
  let cU: class U
  let cN: class N
  let cX: class X
  assume unitnegcl.1: |- U = ( Unit ` R )
  assume unitnegcl.2: |- N = ( invg ` R )


  assert |- ( ( R e. Ring /\ X e. U ) -> ( N ` X ) e. U )

  proof
    cR
    crg
    wcel
    #
    cX
    cU
    wcel
    #
    wa
    #
    cX
    cN
    cfv
    #
    cR
    cur
    cfv
    #
    cR
    cdsr
    cfv
    #
    wbr
    #
    @3
    @4
    cR
    coppr
    cfv
    #
    cdsr
    cfv
    #
    wbr
    #
    @3
    cU
    wcel
    @2
    @0
    @3
    cX
    @5
    wbr
    cX
    @4
    @5
    wbr
    #
    @6
    @0
    @1
    simpl
    @2
    @3
    @3
    cN
    cfv
    #
    cX
    @5
    @0
    @1
    @3
    cR
    cbs
    cfv
    #
    wcel
    #
    @3
    @11
    @5
    wbr
    @0
    cR
    cgrp
    wcel
    #
    cX
    @12
    wcel
    #
    @13
    @1
    cR
    ringgrp
    #
    @12
    cR
    cU
    cX
    @12
    eqid
    #
    unitnegcl.1
    unitcl
    #
    @12
    cR
    cN
    cX
    @17
    unitnegcl.2
    grpinvcl
    syl2an
    #
    @12
    @5
    cR
    cN
    @3
    @17
    @5
    eqid
    #
    unitnegcl.2
    dvdsrneg
    syldan
    @0
    @14
    @15
    @11
    cX
    wceq
    @1
    @16
    @18
    @12
    cR
    cN
    cX
    @17
    unitnegcl.2
    grpinvinv
    syl2an
    #
    breqtrd
    @2
    @10
    cX
    @4
    @8
    wbr
    #
    @2
    @1
    @10
    @22
    wa
    @0
    @1
    simpr
    @5
    cR
    @7
    cU
    @4
    @8
    cX
    unitnegcl.1
    @4
    eqid
    #
    @20
    @7
    eqid
    #
    @8
    eqid
    #
    isunit
    sylib
    #
    simpld
    @12
    @5
    cR
    @4
    @3
    cX
    @17
    @20
    dvdsrtr
    syl3anc
    @2
    @7
    crg
    wcel
    #
    @3
    cX
    @8
    wbr
    @22
    @9
    @0
    @27
    @1
    cR
    @7
    @24
    opprring
    adantr
    #
    @2
    @3
    @11
    cX
    @8
    @2
    @27
    @13
    @3
    @11
    @8
    wbr
    @28
    @19
    @12
    @8
    @7
    cN
    @3
    @12
    cR
    @7
    @24
    @17
    opprbas
    #
    @25
    cR
    cN
    @7
    @24
    unitnegcl.2
    opprneg
    dvdsrneg
    syl2anc
    @21
    breqtrd
    @2
    @10
    @22
    @26
    simprd
    @12
    @8
    @7
    @4
    @3
    cX
    @29
    @25
    dvdsrtr
    syl3anc
    @5
    cR
    @7
    cU
    @4
    @8
    @3
    unitnegcl.1
    @23
    @20
    @24
    @25
    isunit
    sylanbrc
end
