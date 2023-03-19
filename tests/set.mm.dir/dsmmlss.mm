include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "wral.mm"
include "csca.mm"
include "cbs.mm"
include "crg.mm"
include "clmod.mm"
include "wf.mm"
include "cgrp.mm"
include "wss.mm"
include "lmodgrp.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "dsmmsubg.mm"
include "wa.mm"
include "c0g.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "prdslmodd.mm"
include "adantr.mm"
include "simprl.mm"
include "simprr.mm"
include "wb.mm"
include "cdsmm.mm"
include "eqid.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "dsmmelbas.mm"
include "mpbid.mm"
include "simpld.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "simprd.mm"
include "wceq.mm"
include "ad2antrr.mm"
include "cvv.mm"
include "fex.mm"
include "syl2anc.mm"
include "prdssca.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "adantrr.mm"
include "simpr.mm"
include "prdsvscafval.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "simplrl.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"
include "lmodvs0.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impr.mm"
include "expr.mm"
include "necon3d.mm"
include "ss2rabdv.mm"
include "ssfi.mm"
include "mpbir2and.mm"
include "ralrimivva.mm"
include "islss4.mm"

theorem dsmmlss
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume dsmmlss.i: |- ( ph -> I e. W )
  assume dsmmlss.s: |- ( ph -> S e. Ring )
  assume dsmmlss.r: |- ( ph -> R : I --> LMod )
  assume dsmmlss.k: |- ( ( ph /\ x e. I ) -> ( Scalar ` ( R ` x ) ) = S )
  assume dsmmlss.p: |- P = ( S Xs_ R )
  assume dsmmlss.u: |- U = ( LSubSp ` P )
  assume dsmmlss.h: |- H = ( Base ` ( S (+)m R ) )

  disjoint ph x
  disjoint S x
  disjoint R x
  disjoint I x
  disjoint P x
  disjoint H x
  disjoint a ph
  disjoint b ph
  disjoint a b
  disjoint a x
  disjoint b x
  disjoint S a
  disjoint S b
  disjoint R a
  disjoint R b
  disjoint I a
  disjoint I b
  disjoint P a
  disjoint P b
  disjoint U a
  disjoint U b
  disjoint H a
  disjoint H b
  assert |- ( ph -> H e. U )

  proof
    wph
    cH
    cU
    wcel
    #
    cH
    cP
    csubg
    cfv
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cP
    cvsca
    cfv
    #
    co
    #
    cH
    wcel
    #
    vb
    cH
    wral
    va
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wral
    #
    wph
    cP
    cR
    cS
    cH
    cI
    crg
    cW
    dsmmlss.p
    dsmmlss.h
    dsmmlss.i
    dsmmlss.s
    wph
    cI
    clmod
    cR
    wf
    #
    clmod
    cgrp
    wss
    cI
    cgrp
    cR
    wf
    dsmmlss.r
    va
    clmod
    cgrp
    @2
    lmodgrp
    ssriv
    cI
    clmod
    cgrp
    cR
    fss
    sylancl
    dsmmsubg
    wph
    @6
    va
    vb
    @8
    cH
    wph
    @2
    @8
    wcel
    #
    @3
    cH
    wcel
    #
    wa
    #
    wa
    #
    @6
    @5
    cP
    cbs
    cfv
    #
    wcel
    #
    vx
    cv
    #
    @5
    cfv
    #
    @17
    cR
    cfv
    #
    c0g
    cfv
    #
    wne
    #
    vx
    cI
    crab
    #
    cfn
    wcel
    #
    @14
    cP
    clmod
    wcel
    #
    @11
    @3
    @15
    wcel
    #
    @16
    wph
    @24
    @13
    wph
    vx
    cR
    cS
    cI
    cW
    cP
    dsmmlss.p
    dsmmlss.s
    dsmmlss.i
    dsmmlss.r
    dsmmlss.k
    prdslmodd
    #
    adantr
    wph
    @11
    @12
    simprl
    @14
    @25
    @17
    @3
    cfv
    #
    @20
    wne
    #
    vx
    cI
    crab
    #
    cfn
    wcel
    #
    @14
    @12
    @25
    @30
    wa
    #
    wph
    @11
    @12
    simprr
    wph
    @12
    @31
    wb
    @13
    wph
    @15
    cS
    cR
    cdsmm
    co
    #
    cP
    cR
    cS
    cH
    cI
    cW
    @3
    vx
    dsmmlss.p
    @32
    eqid
    #
    @15
    eqid
    #
    dsmmlss.h
    dsmmlss.i
    wph
    @10
    cR
    cI
    wfn
    #
    dsmmlss.r
    cI
    clmod
    cR
    ffn
    syl
    #
    dsmmelbas
    adantr
    mpbid
    #
    simpld
    #
    @2
    @4
    @7
    @8
    @15
    cP
    @3
    @34
    @7
    eqid
    #
    @4
    eqid
    #
    @8
    eqid
    #
    lmodvscl
    syl3anc
    @14
    @30
    @22
    @29
    wss
    @23
    @14
    @25
    @30
    @37
    simprd
    @14
    @21
    @28
    vx
    cI
    @14
    @17
    cI
    wcel
    #
    wa
    #
    @27
    @20
    @18
    @20
    @14
    @42
    @27
    @20
    wceq
    #
    @18
    @20
    wceq
    @14
    @42
    @44
    wa
    wa
    @18
    @2
    @27
    @19
    cvsca
    cfv
    #
    co
    #
    @20
    @14
    @42
    @18
    @46
    wceq
    @44
    @43
    @15
    cR
    cS
    @4
    @2
    @3
    cI
    @17
    cS
    cbs
    cfv
    #
    crg
    cW
    cP
    dsmmlss.p
    @34
    @40
    @47
    eqid
    wph
    cS
    crg
    wcel
    @13
    @42
    dsmmlss.s
    ad2antrr
    wph
    cI
    cW
    wcel
    #
    @13
    @42
    dsmmlss.i
    ad2antrr
    wph
    @35
    @13
    @42
    @36
    ad2antrr
    @14
    @2
    @47
    wcel
    #
    @42
    wph
    @11
    @49
    @12
    wph
    @49
    @11
    wph
    @47
    @8
    @2
    wph
    cS
    @7
    cbs
    wph
    cP
    cR
    cS
    crg
    cvv
    dsmmlss.p
    dsmmlss.s
    wph
    @10
    @48
    cR
    cvv
    wcel
    dsmmlss.r
    dsmmlss.i
    cI
    clmod
    cW
    cR
    fex
    syl2anc
    prdssca
    #
    fveq2d
    eleq2d
    biimpar
    adantrr
    adantr
    @14
    @25
    @42
    @38
    adantr
    @14
    @42
    simpr
    prdsvscafval
    adantrr
    @14
    @42
    @44
    @46
    @20
    wceq
    #
    @43
    @51
    @44
    @2
    @20
    @45
    co
    #
    @20
    wceq
    #
    @43
    @19
    clmod
    wcel
    #
    @2
    @19
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    @53
    wph
    @42
    @54
    @13
    wph
    cI
    clmod
    @17
    cR
    dsmmlss.r
    ffvelrnda
    adantlr
    @43
    @2
    @8
    @56
    wph
    @11
    @12
    @42
    simplrl
    wph
    @42
    @56
    @8
    wceq
    @13
    wph
    @42
    wa
    #
    @55
    @7
    cbs
    @57
    @55
    cS
    @7
    dsmmlss.k
    wph
    cS
    @7
    wceq
    @42
    @50
    adantr
    eqtrd
    fveq2d
    adantlr
    eleqtrrd
    @45
    @55
    @56
    @19
    @2
    @20
    @55
    eqid
    @45
    eqid
    @56
    eqid
    @20
    eqid
    lmodvs0
    syl2anc
    @44
    @46
    @52
    @20
    @27
    @20
    @2
    @45
    oveq2
    eqeq1d
    syl5ibrcom
    impr
    eqtrd
    expr
    necon3d
    ss2rabdv
    @29
    @22
    ssfi
    syl2anc
    wph
    @6
    @16
    @23
    wa
    wb
    @13
    wph
    @15
    @32
    cP
    cR
    cS
    cH
    cI
    cW
    @5
    vx
    dsmmlss.p
    @33
    @34
    dsmmlss.h
    dsmmlss.i
    @36
    dsmmelbas
    adantr
    mpbir2and
    ralrimivva
    wph
    @24
    @0
    @1
    @9
    wa
    wb
    @26
    @8
    cU
    @4
    cH
    @7
    @15
    cP
    va
    vb
    @39
    @41
    @34
    @40
    dsmmlss.u
    islss4
    syl
    mpbir2and
end
