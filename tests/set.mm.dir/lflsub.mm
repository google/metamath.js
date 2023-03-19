include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cur.mm"
include "cfv.mm"
include "cminusg.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "cmulr.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3l.mm"
include "cbs.mm"
include "cgrp.mm"
include "crg.mm"
include "lmodring.mm"
include "3ad2ant1.mm"
include "ringgrp.mm"
include "syl.mm"
include "eqid.mm"
include "ringidcl.mm"
include "grpinvcl.mm"
include "syl2anc.mm"
include "simp3r.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "lmodcom.mm"
include "fveq2d.mm"
include "simp2.mm"
include "lfli.mm"
include "syl113anc.mm"
include "lflcl.mm"
include "3adant3l.mm"
include "ringnegl.mm"
include "oveq1d.mm"
include "cabl.mm"
include "ringabl.mm"
include "3adant3r.mm"
include "ablcom.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "lmodvsubval2.mm"
include "grpsubval.mm"
include "3eqtr4d.mm"

theorem lflsub
  let cD: class D
  let cF: class F
  let cG: class G
  let cM: class M
  let c.mi: class .-
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume lflsub.d: |- D = ( Scalar ` W )
  assume lflsub.m: |- M = ( -g ` D )
  assume lflsub.v: |- V = ( Base ` W )
  assume lflsub.a: |- .- = ( -g ` W )
  assume lflsub.f: |- F = ( LFnl ` W )


  assert |- ( ( W e. LMod /\ G e. F /\ ( X e. V /\ Y e. V ) ) -> ( G ` ( X .- Y ) ) = ( ( G ` X ) M ( G ` Y ) ) )

  proof
    cW
    clmod
    wcel
    #
    cG
    cF
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    wa
    #
    w3a
    #
    cX
    cD
    cur
    cfv
    #
    cD
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
    cG
    cfv
    #
    cX
    cG
    cfv
    #
    cY
    cG
    cfv
    #
    @7
    cfv
    #
    cD
    cplusg
    cfv
    #
    co
    #
    cX
    cY
    c.mi
    co
    #
    cG
    cfv
    @14
    @15
    cM
    co
    #
    @5
    @13
    @10
    cX
    @11
    co
    #
    cG
    cfv
    #
    @8
    @15
    cD
    cmulr
    cfv
    #
    co
    #
    @14
    @17
    co
    #
    @18
    @5
    @12
    @21
    cG
    @5
    @0
    @2
    @10
    cV
    wcel
    #
    @12
    @21
    wceq
    @0
    @1
    @4
    simp1
    #
    @0
    @1
    @2
    @3
    simp3l
    #
    @5
    @0
    @8
    cD
    cbs
    cfv
    #
    wcel
    #
    @3
    @26
    @27
    @5
    cD
    cgrp
    wcel
    #
    @6
    @29
    wcel
    #
    @30
    @5
    cD
    crg
    wcel
    #
    @31
    @0
    @1
    @33
    @4
    cD
    cW
    lflsub.d
    lmodring
    3ad2ant1
    #
    cD
    ringgrp
    syl
    #
    @5
    @33
    @32
    @34
    @29
    cD
    @6
    @29
    eqid
    #
    @6
    eqid
    #
    ringidcl
    syl
    @29
    cD
    @7
    @6
    @36
    @7
    eqid
    #
    grpinvcl
    syl2anc
    #
    @0
    @1
    @2
    @3
    simp3r
    #
    @8
    @9
    cD
    @29
    cV
    cW
    cY
    lflsub.v
    lflsub.d
    @9
    eqid
    #
    @36
    lmodvscl
    syl3anc
    @11
    cV
    cW
    cX
    @10
    lflsub.v
    @11
    eqid
    #
    lmodcom
    syl3anc
    fveq2d
    @5
    @0
    @1
    @30
    @3
    @2
    @22
    @25
    wceq
    @27
    @0
    @1
    @4
    simp2
    @39
    @40
    @28
    cD
    @11
    @17
    @8
    @9
    @23
    cF
    cG
    @29
    cV
    cW
    cY
    cX
    clmod
    lflsub.v
    @42
    lflsub.d
    @41
    @36
    @17
    eqid
    #
    @23
    eqid
    #
    lflsub.f
    lfli
    syl113anc
    @5
    @25
    @16
    @14
    @17
    co
    #
    @18
    @5
    @24
    @16
    @14
    @17
    @5
    @29
    cD
    @23
    @6
    @7
    @15
    @36
    @44
    @37
    @38
    @34
    @0
    @1
    @3
    @15
    @29
    wcel
    #
    @2
    cD
    cF
    cG
    @29
    cV
    cW
    cY
    clmod
    lflsub.d
    @36
    lflsub.v
    lflsub.f
    lflcl
    3adant3l
    #
    ringnegl
    oveq1d
    @5
    cD
    cabl
    wcel
    #
    @16
    @29
    wcel
    #
    @14
    @29
    wcel
    #
    @45
    @18
    wceq
    @5
    @33
    @48
    @34
    cD
    ringabl
    syl
    @5
    @31
    @46
    @49
    @35
    @47
    @29
    cD
    @7
    @15
    @36
    @38
    grpinvcl
    syl2anc
    @0
    @1
    @2
    @50
    @3
    cD
    cF
    cG
    @29
    cV
    cW
    cX
    clmod
    lflsub.d
    @36
    lflsub.v
    lflsub.f
    lflcl
    3adant3r
    #
    @29
    @17
    cD
    @16
    @14
    @36
    @43
    ablcom
    syl3anc
    eqtrd
    3eqtrd
    @5
    @19
    @12
    cG
    @5
    @0
    @2
    @3
    @19
    @12
    wceq
    @27
    @28
    @40
    cX
    cY
    @11
    @9
    @6
    cD
    c.mi
    @7
    cV
    cW
    lflsub.v
    @42
    lflsub.a
    lflsub.d
    @41
    @38
    @37
    lmodvsubval2
    syl3anc
    fveq2d
    @5
    @50
    @46
    @20
    @18
    wceq
    @51
    @47
    @29
    @17
    cD
    @7
    cM
    @14
    @15
    @36
    @43
    @38
    lflsub.m
    grpsubval
    syl2anc
    3eqtr4d
end
