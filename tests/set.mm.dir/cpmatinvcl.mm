include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "wa.mm"
include "cv.mm"
include "cminusg.mm"
include "cfv.mm"
include "co.mm"
include "cascl.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "wral.mm"
include "eqid.mm"
include "cpmatelimp2.mm"
include "csca.mm"
include "wi.mm"
include "ply1sca.mm"
include "adantl.mm"
include "adantr.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpinvcl.mm"
include "sylan.mm"
include "eqeltrd.mm"
include "ex.mm"
include "ad2antrr.mm"
include "imp.mm"
include "wb.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "w3a.mm"
include "ply1ring.mm"
include "ad3antlr.mm"
include "simplr.mm"
include "simpr.mm"
include "3jca.mm"
include "matinvgcell.mm"
include "syl.mm"
include "cghm.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "asclghm.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "ghminv.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "eqtrd.mm"
include "rspcedvd.mm"
include "rexlimdva.mm"
include "ralimdvva.mm"
include "expimpd.mm"
include "syld.mm"
include "simpll.mm"
include "pmatring.mm"
include "cpmatpmat.mm"
include "3expa.mm"
include "cpmatel2.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "ralrimiva.mm"

theorem cpmatinvcl
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cR: class R
  let cS: class S
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  assume cpmatsrngpmat.s: |- S = ( N ConstPolyMat R )
  assume cpmatsrngpmat.p: |- P = ( Poly1 ` R )
  assume cpmatsrngpmat.c: |- C = ( N Mat P )

  disjoint N x
  disjoint R x
  disjoint C i
  disjoint C j
  disjoint C n
  disjoint i j
  disjoint i n
  disjoint j n
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint R i
  disjoint R j
  disjoint R n
  disjoint C a
  disjoint C b
  disjoint C c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint N y
  disjoint a i
  disjoint a j
  disjoint a x
  disjoint a y
  disjoint b i
  disjoint b j
  disjoint b x
  disjoint b y
  disjoint c i
  disjoint c j
  disjoint c x
  disjoint c y
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint x y
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R y
  disjoint S y
  assert |- ( ( N e. Fin /\ R e. Ring ) -> A. x e. S ( ( invg ` C ) ` x ) e. S )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    wa
    #
    vx
    cv
    #
    cC
    cminusg
    cfv
    #
    cfv
    #
    cS
    wcel
    #
    vx
    cS
    @2
    @3
    cS
    wcel
    #
    wa
    #
    @6
    vi
    cv
    #
    vj
    cv
    #
    @5
    co
    #
    vc
    cv
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    wceq
    #
    vc
    cR
    cbs
    cfv
    #
    wrex
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @2
    @7
    @18
    @2
    @7
    @3
    cC
    cbs
    cfv
    #
    wcel
    #
    @9
    @10
    @3
    co
    #
    va
    cv
    #
    @13
    cfv
    #
    wceq
    #
    va
    @16
    wrex
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    wa
    @18
    @13
    @19
    cC
    cP
    cR
    cS
    vi
    vj
    va
    @16
    @3
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @19
    eqid
    #
    @16
    eqid
    #
    @13
    eqid
    #
    cpmatelimp2
    @2
    @20
    @26
    @18
    @2
    @20
    wa
    #
    @25
    @17
    vi
    vj
    cN
    cN
    @30
    @9
    cN
    wcel
    @10
    cN
    wcel
    wa
    #
    wa
    #
    @24
    @17
    va
    @16
    @32
    @22
    @16
    wcel
    #
    wa
    #
    @24
    @17
    @34
    @24
    wa
    #
    @15
    @11
    @22
    cP
    csca
    cfv
    #
    cminusg
    cfv
    #
    cfv
    #
    @13
    cfv
    #
    wceq
    #
    vc
    @38
    @16
    @34
    @38
    @16
    wcel
    #
    @24
    @32
    @33
    @41
    @2
    @33
    @41
    wi
    @20
    @31
    @2
    @33
    @41
    @2
    @33
    wa
    #
    @38
    @22
    cR
    cminusg
    cfv
    #
    cfv
    #
    @16
    @42
    @22
    @37
    @43
    @42
    @36
    cR
    cminusg
    @42
    cR
    @36
    @2
    cR
    @36
    wceq
    #
    @33
    @1
    @45
    @0
    cP
    cR
    crg
    cpmatsrngpmat.p
    ply1sca
    adantl
    #
    adantr
    eqcomd
    fveq2d
    fveq1d
    @2
    cR
    cgrp
    wcel
    #
    @33
    @44
    @16
    wcel
    @1
    @47
    @0
    cR
    ringgrp
    adantl
    @16
    cR
    @43
    @22
    @28
    @43
    eqid
    grpinvcl
    sylan
    eqeltrd
    ex
    ad2antrr
    imp
    adantr
    @12
    @38
    wceq
    #
    @15
    @40
    wb
    @35
    @48
    @14
    @39
    @11
    @12
    @38
    @13
    fveq2
    eqeq2d
    adantl
    @35
    @11
    @21
    cP
    cminusg
    cfv
    #
    cfv
    #
    @39
    @35
    cP
    crg
    wcel
    #
    @20
    @31
    w3a
    #
    @11
    @50
    wceq
    @32
    @52
    @33
    @24
    @32
    @51
    @20
    @31
    @1
    @51
    @0
    @20
    @31
    cP
    cR
    cpmatsrngpmat.p
    ply1ring
    ad3antlr
    #
    @2
    @20
    @31
    simplr
    @30
    @31
    simpr
    3jca
    ad2antrr
    cC
    @19
    cP
    @9
    @10
    cN
    @49
    @4
    @3
    cpmatsrngpmat.c
    @27
    @49
    eqid
    #
    @4
    eqid
    #
    matinvgcell
    syl
    @24
    @34
    @50
    @23
    @49
    cfv
    #
    @39
    @21
    @23
    @49
    fveq2
    @34
    @39
    @56
    @34
    @13
    @36
    cP
    cghm
    co
    wcel
    @22
    @36
    cbs
    cfv
    #
    wcel
    #
    @39
    @56
    wceq
    @34
    @13
    @36
    cP
    @29
    @36
    eqid
    @32
    @51
    @33
    @53
    adantr
    @32
    cP
    clmod
    wcel
    #
    @33
    @1
    @59
    @0
    @20
    @31
    cP
    cR
    cpmatsrngpmat.p
    ply1lmod
    ad3antlr
    adantr
    asclghm
    @32
    @33
    @58
    @2
    @33
    @58
    wi
    @20
    @31
    @2
    @33
    @58
    @2
    @16
    @57
    @22
    @2
    cR
    @36
    cbs
    @46
    fveq2d
    eleq2d
    biimpd
    ad2antrr
    imp
    @57
    @36
    cP
    @13
    @37
    @49
    @22
    @57
    eqid
    @37
    eqid
    @54
    ghminv
    syl2anc
    eqcomd
    sylan9eqr
    eqtrd
    rspcedvd
    ex
    rexlimdva
    ralimdvva
    expimpd
    syld
    imp
    @8
    @0
    @1
    @5
    @19
    wcel
    #
    @6
    @18
    wb
    @0
    @1
    @7
    simpll
    @0
    @1
    @7
    simplr
    @8
    cC
    cgrp
    wcel
    #
    @20
    @60
    @2
    @61
    @7
    @2
    cC
    crg
    wcel
    @61
    cC
    cP
    cR
    cN
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    pmatring
    cC
    ringgrp
    syl
    adantr
    @0
    @1
    @7
    @20
    @19
    cC
    cP
    cR
    cS
    @3
    cN
    crg
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @27
    cpmatpmat
    3expa
    @19
    cC
    @4
    @3
    @27
    @55
    grpinvcl
    syl2anc
    @13
    @19
    cC
    cP
    cR
    cS
    vi
    vj
    vc
    @16
    @5
    cN
    cpmatsrngpmat.s
    cpmatsrngpmat.p
    cpmatsrngpmat.c
    @27
    @28
    @29
    cpmatel2
    syl3anc
    mpbird
    ralrimiva
end
