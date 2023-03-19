include "clvec.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "w3a.mm"
include "csn.mm"
include "co.mm"
include "clss.mm"
include "wss.mm"
include "clmod.mm"
include "lveclmod.mm"
include "3ad2ant1.mm"
include "simp2r.mm"
include "eqid.mm"
include "lkrlss.mm"
include "syl2anc.mm"
include "simp2l.mm"
include "lspsncl.mm"
include "lsmcl.mm"
include "syl3anc.mm"
include "lssss.mm"
include "syl.mm"
include "cv.mm"
include "cinvr.mm"
include "cmulr.mm"
include "cvsca.mm"
include "csg.mm"
include "cplusg.mm"
include "wceq.mm"
include "simpl1.mm"
include "simpr.mm"
include "cbs.mm"
include "crg.mm"
include "lmodring.mm"
include "simpl2r.mm"
include "lflcl.mm"
include "cdr.mm"
include "lvecdrng.mm"
include "simpl2l.mm"
include "simpl3.mm"
include "drnginvrcl.mm"
include "ringcl.mm"
include "lmodvscl.mm"
include "lmodvnpcan.mm"
include "csubg.mm"
include "lsssssubg.mm"
include "adantr.mm"
include "sseldd.mm"
include "lmodvsubcl.mm"
include "lflsub.mm"
include "syl112anc.mm"
include "lflmul.mm"
include "ringass.mm"
include "syl13anc.mm"
include "cur.mm"
include "drnginvrl.mm"
include "oveq2d.mm"
include "ringridm.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "grpsubid.mm"
include "wb.mm"
include "ellkr.mm"
include "mpbir2and.mm"
include "lspsneli.mm"
include "lsmelvali.mm"
include "syl22anc.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"

theorem lkrlsp
  let cD: class D
  let c.po: class .(+)
  let cF: class F
  let cG: class G
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vu: setvar u
  assume lkrlsp.d: |- D = ( Scalar ` W )
  assume lkrlsp.o: |- .0. = ( 0g ` D )
  assume lkrlsp.v: |- V = ( Base ` W )
  assume lkrlsp.n: |- N = ( LSpan ` W )
  assume lkrlsp.p: |- .(+) = ( LSSum ` W )
  assume lkrlsp.f: |- F = ( LFnl ` W )
  assume lkrlsp.k: |- K = ( LKer ` W )


  assert |- ( ( W e. LVec /\ ( X e. V /\ G e. F ) /\ ( G ` X ) =/= .0. ) -> ( ( K ` G ) .(+) ( N ` { X } ) ) = V )

  proof
    cW
    clvec
    wcel
    #
    cX
    cV
    wcel
    #
    cG
    cF
    wcel
    #
    wa
    #
    cX
    cG
    cfv
    #
    c.0
    wne
    #
    w3a
    #
    cG
    cK
    cfv
    #
    cX
    csn
    cN
    cfv
    #
    c.po
    co
    #
    cV
    @6
    @9
    cW
    clss
    cfv
    #
    wcel
    #
    @9
    cV
    wss
    @6
    cW
    clmod
    wcel
    #
    @7
    @10
    wcel
    #
    @8
    @10
    wcel
    #
    @11
    @0
    @3
    @12
    @5
    cW
    lveclmod
    #
    3ad2ant1
    #
    @6
    @12
    @2
    @13
    @16
    @0
    @1
    @2
    @5
    simp2r
    @10
    cF
    cG
    cK
    cW
    lkrlsp.f
    lkrlsp.k
    @10
    eqid
    #
    lkrlss
    syl2anc
    #
    @6
    @12
    @1
    @14
    @16
    @0
    @1
    @2
    @5
    simp2l
    @10
    cN
    cV
    cW
    cX
    lkrlsp.v
    @17
    lkrlsp.n
    lspsncl
    syl2anc
    #
    c.po
    @10
    @7
    @8
    cW
    @17
    lkrlsp.p
    lsmcl
    syl3anc
    @10
    @9
    cV
    cW
    lkrlsp.v
    @17
    lssss
    syl
    @6
    vu
    cV
    @9
    @6
    vu
    cv
    #
    cV
    wcel
    #
    @20
    @9
    wcel
    @6
    @21
    wa
    #
    @20
    @20
    cG
    cfv
    #
    @4
    cD
    cinvr
    cfv
    #
    cfv
    #
    cD
    cmulr
    cfv
    #
    co
    #
    cX
    cW
    cvsca
    cfv
    #
    co
    #
    cW
    csg
    cfv
    #
    co
    #
    @29
    cW
    cplusg
    cfv
    #
    co
    #
    @20
    @9
    @22
    @12
    @21
    @29
    cV
    wcel
    #
    @33
    @20
    wceq
    @22
    @0
    @12
    @0
    @3
    @5
    @21
    simpl1
    #
    @15
    syl
    #
    @6
    @21
    simpr
    #
    @22
    @12
    @27
    cD
    cbs
    cfv
    #
    wcel
    #
    @1
    @34
    @36
    @22
    cD
    crg
    wcel
    #
    @23
    @38
    wcel
    #
    @25
    @38
    wcel
    #
    @39
    @22
    @12
    @40
    @36
    cD
    cW
    lkrlsp.d
    lmodring
    syl
    #
    @22
    @0
    @2
    @21
    @41
    @35
    @1
    @2
    @0
    @5
    @21
    simpl2r
    #
    @37
    cD
    cF
    cG
    @38
    cV
    cW
    @20
    clvec
    lkrlsp.d
    @38
    eqid
    #
    lkrlsp.v
    lkrlsp.f
    lflcl
    syl3anc
    #
    @22
    cD
    cdr
    wcel
    #
    @4
    @38
    wcel
    #
    @5
    @42
    @22
    @0
    @47
    @35
    cD
    cW
    lkrlsp.d
    lvecdrng
    syl
    #
    @22
    @0
    @2
    @1
    @48
    @35
    @44
    @1
    @2
    @0
    @5
    @21
    simpl2l
    #
    cD
    cF
    cG
    @38
    cV
    cW
    cX
    clvec
    lkrlsp.d
    @45
    lkrlsp.v
    lkrlsp.f
    lflcl
    syl3anc
    #
    @0
    @3
    @5
    @21
    simpl3
    #
    @38
    cD
    @24
    @4
    c.0
    @45
    lkrlsp.o
    @24
    eqid
    #
    drnginvrcl
    syl3anc
    #
    @38
    cD
    @26
    @23
    @25
    @45
    @26
    eqid
    #
    ringcl
    syl3anc
    #
    @50
    @27
    @28
    cD
    @38
    cV
    cW
    cX
    lkrlsp.v
    lkrlsp.d
    @28
    eqid
    #
    @45
    lmodvscl
    syl3anc
    #
    @20
    @29
    @32
    @30
    cV
    cW
    lkrlsp.v
    @32
    eqid
    #
    @30
    eqid
    #
    lmodvnpcan
    syl3anc
    @22
    @7
    cW
    csubg
    cfv
    #
    wcel
    @8
    @61
    wcel
    @31
    @7
    wcel
    #
    @29
    @8
    wcel
    @33
    @9
    wcel
    @22
    @10
    @61
    @7
    @22
    @12
    @10
    @61
    wss
    @36
    @10
    cW
    @17
    lsssssubg
    syl
    #
    @6
    @13
    @21
    @18
    adantr
    sseldd
    @22
    @10
    @61
    @8
    @63
    @6
    @14
    @21
    @19
    adantr
    sseldd
    @22
    @62
    @31
    cV
    wcel
    #
    @31
    cG
    cfv
    #
    c.0
    wceq
    #
    @22
    @12
    @21
    @34
    @64
    @36
    @37
    @58
    @30
    cV
    cW
    @20
    @29
    lkrlsp.v
    @60
    lmodvsubcl
    syl3anc
    @22
    @65
    @23
    @29
    cG
    cfv
    #
    cD
    csg
    cfv
    #
    co
    #
    @23
    @23
    @68
    co
    #
    c.0
    @22
    @12
    @2
    @21
    @34
    @65
    @69
    wceq
    @36
    @44
    @37
    @58
    cD
    cF
    cG
    @68
    @30
    cV
    cW
    @20
    @29
    lkrlsp.d
    @68
    eqid
    #
    lkrlsp.v
    @60
    lkrlsp.f
    lflsub
    syl112anc
    @22
    @67
    @23
    @23
    @68
    @22
    @67
    @27
    @4
    @26
    co
    #
    @23
    @25
    @4
    @26
    co
    #
    @26
    co
    #
    @23
    @22
    @12
    @2
    @39
    @1
    @67
    @72
    wceq
    @36
    @44
    @56
    @50
    cD
    @27
    @28
    @26
    cF
    cG
    @38
    cV
    cW
    cX
    lkrlsp.d
    @45
    @55
    lkrlsp.v
    @57
    lkrlsp.f
    lflmul
    syl112anc
    @22
    @40
    @41
    @42
    @48
    @72
    @74
    wceq
    @43
    @46
    @54
    @51
    @38
    cD
    @26
    @23
    @25
    @4
    @45
    @55
    ringass
    syl13anc
    @22
    @74
    @23
    cD
    cur
    cfv
    #
    @26
    co
    #
    @23
    @22
    @73
    @75
    @23
    @26
    @22
    @47
    @48
    @5
    @73
    @75
    wceq
    @49
    @51
    @52
    @38
    cD
    @26
    @75
    @24
    @4
    c.0
    @45
    lkrlsp.o
    @55
    @75
    eqid
    #
    @53
    drnginvrl
    syl3anc
    oveq2d
    @22
    @40
    @41
    @76
    @23
    wceq
    @43
    @46
    @38
    cD
    @26
    @75
    @23
    @45
    @55
    @77
    ringridm
    syl2anc
    eqtrd
    3eqtrd
    oveq2d
    @22
    cD
    cgrp
    wcel
    #
    @41
    @70
    c.0
    wceq
    @22
    @12
    @78
    @36
    cD
    cW
    lkrlsp.d
    lmodfgrp
    syl
    @46
    @38
    cD
    @68
    @23
    c.0
    @45
    lkrlsp.o
    @71
    grpsubid
    syl2anc
    3eqtrd
    @22
    @0
    @2
    @62
    @64
    @66
    wa
    wb
    @35
    @44
    cD
    cF
    cG
    cK
    cV
    cW
    @31
    clvec
    c.0
    lkrlsp.v
    lkrlsp.d
    lkrlsp.o
    lkrlsp.f
    lkrlsp.k
    ellkr
    syl2anc
    mpbir2and
    @22
    @27
    @28
    cD
    @38
    cN
    cV
    cW
    cX
    lkrlsp.v
    @57
    lkrlsp.d
    @45
    lkrlsp.n
    @36
    @56
    @50
    lspsneli
    @32
    c.po
    @7
    @8
    cW
    @31
    @29
    @59
    lkrlsp.p
    lsmelvali
    syl22anc
    eqeltrrd
    ex
    ssrdv
    eqssd
end
