include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "cminusg.mm"
include "cvsca.mm"
include "cplusg.mm"
include "cbs.mm"
include "wceq.mm"
include "simpll.mm"
include "eqid.mm"
include "lssel.mm"
include "ad2ant2lr.mm"
include "ad2ant2l.mm"
include "lmodvsubval2.mm"
include "syl3anc.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "syl.mm"
include "lmod1cl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "lmodvscl.mm"
include "lmodcom.mm"
include "simplr.mm"
include "simprr.mm"
include "simprl.mm"
include "lsscl.mm"
include "syl13anc.mm"
include "eqeltrd.mm"

theorem lssvsubcl
  let cS: class S
  let cU: class U
  let c.mi: class .-
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lssvsubcl.m: |- .- = ( -g ` W )
  assume lssvsubcl.s: |- S = ( LSubSp ` W )


  assert |- ( ( ( W e. LMod /\ U e. S ) /\ ( X e. U /\ Y e. U ) ) -> ( X .- Y ) e. U )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    wa
    #
    wa
    #
    cX
    cY
    c.mi
    co
    #
    cX
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
    cY
    cW
    cvsca
    cfv
    #
    co
    #
    cW
    cplusg
    cfv
    #
    co
    #
    cU
    @6
    @0
    cX
    cW
    cbs
    cfv
    #
    wcel
    #
    cY
    @16
    wcel
    #
    @7
    @15
    wceq
    @0
    @1
    @5
    simpll
    #
    @1
    @3
    @17
    @0
    @4
    cS
    cU
    @16
    cW
    cX
    @16
    eqid
    #
    lssvsubcl.s
    lssel
    ad2ant2lr
    #
    @1
    @4
    @18
    @0
    @3
    cS
    cU
    @16
    cW
    cY
    @20
    lssvsubcl.s
    lssel
    ad2ant2l
    #
    cX
    cY
    @14
    @12
    @9
    @8
    c.mi
    @10
    @16
    cW
    @20
    @14
    eqid
    #
    lssvsubcl.m
    @8
    eqid
    #
    @12
    eqid
    #
    @10
    eqid
    #
    @9
    eqid
    #
    lmodvsubval2
    syl3anc
    @6
    @15
    @13
    cX
    @14
    co
    #
    cU
    @6
    @0
    @17
    @13
    @16
    wcel
    #
    @15
    @28
    wceq
    @19
    @21
    @6
    @0
    @11
    @8
    cbs
    cfv
    #
    wcel
    #
    @18
    @29
    @19
    @6
    @8
    cgrp
    wcel
    #
    @9
    @30
    wcel
    #
    @31
    @6
    @0
    @32
    @19
    @8
    cW
    @24
    lmodfgrp
    syl
    @6
    @0
    @33
    @19
    @9
    @8
    @30
    cW
    @24
    @30
    eqid
    #
    @27
    lmod1cl
    syl
    @30
    @8
    @10
    @9
    @34
    @26
    grpinvcl
    syl2anc
    #
    @22
    @11
    @12
    @8
    @30
    @16
    cW
    cY
    @20
    @24
    @25
    @34
    lmodvscl
    syl3anc
    @14
    @16
    cW
    cX
    @13
    @20
    @23
    lmodcom
    syl3anc
    @6
    @1
    @31
    @4
    @3
    @28
    cU
    wcel
    @0
    @1
    @5
    simplr
    @35
    @2
    @3
    @4
    simprr
    @2
    @3
    @4
    simprl
    @30
    @14
    cS
    @12
    cU
    @8
    cW
    cY
    cX
    @11
    @24
    @34
    @23
    @25
    lssvsubcl.s
    lsscl
    syl13anc
    eqeltrd
    eqeltrd
end
