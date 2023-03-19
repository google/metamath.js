include "cplusg.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "c0g.mm"
include "eqidd.mm"
include "cdsmm.mm"
include "cbs.mm"
include "cprds.mm"
include "cv.mm"
include "wne.mm"
include "cdm.mm"
include "crab.mm"
include "cfn.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "cgrp.mm"
include "wf.mm"
include "fex.mm"
include "syl2anc.mm"
include "eqid.mm"
include "dsmmbase.mm"
include "syl.mm"
include "ssrab2.mm"
include "syl6eqssr.mm"
include "fveq2i.mm"
include "3sstr4g.mm"
include "cmnd.mm"
include "wss.mm"
include "grpmnd.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "dsmm0cl.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "dsmmacl.mm"
include "wa.mm"
include "cminusg.mm"
include "prdsgrpd.mm"
include "adantr.mm"
include "sselda.mm"
include "grpinvcl.mm"
include "simpr.mm"
include "wfn.mm"
include "ffn.mm"
include "dsmmelbas.mm"
include "mpbid.mm"
include "simprd.mm"
include "ad2antrr.mm"
include "prdsinvgd2.mm"
include "adantrr.mm"
include "fveq2.mm"
include "ad2antll.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "grpinvid.mm"
include "3eqtrd.mm"
include "expr.mm"
include "necon3d.mm"
include "ss2rabdv.mm"
include "ssfi.mm"
include "mpbir2and.mm"
include "issubgrpd2.mm"

theorem dsmmsubg
  let wph: wff ph
  let cP: class P
  let cR: class R
  let cS: class S
  let cH: class H
  let cI: class I
  let cV: class V
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume dsmmsubg.p: |- P = ( S Xs_ R )
  assume dsmmsubg.h: |- H = ( Base ` ( S (+)m R ) )
  assume dsmmsubg.i: |- ( ph -> I e. W )
  assume dsmmsubg.s: |- ( ph -> S e. V )
  assume dsmmsubg.r: |- ( ph -> R : I --> Grp )


  assert |- ( ph -> H e. ( SubGrp ` P ) )

  proof
    wph
    va
    vb
    cH
    cP
    cplusg
    cfv
    #
    cP
    cH
    cress
    co
    #
    cP
    cP
    c0g
    cfv
    #
    wph
    @1
    eqidd
    wph
    @2
    eqidd
    wph
    @0
    eqidd
    wph
    cS
    cR
    cdsmm
    co
    #
    cbs
    cfv
    #
    cS
    cR
    cprds
    co
    #
    cbs
    cfv
    #
    cH
    cP
    cbs
    cfv
    #
    wph
    @4
    vb
    cv
    #
    va
    cv
    #
    cfv
    #
    @8
    cR
    cfv
    #
    c0g
    cfv
    #
    wne
    #
    vb
    cR
    cdm
    crab
    cfn
    wcel
    #
    va
    @6
    crab
    #
    @6
    wph
    cR
    cvv
    wcel
    #
    @15
    @4
    wceq
    wph
    cI
    cgrp
    cR
    wf
    #
    cI
    cW
    wcel
    #
    @16
    dsmmsubg.r
    dsmmsubg.i
    cI
    cgrp
    cW
    cR
    fex
    syl2anc
    vb
    @15
    cR
    cS
    va
    cvv
    @15
    eqid
    dsmmbase
    syl
    @14
    va
    @6
    ssrab2
    syl6eqssr
    dsmmsubg.h
    cP
    @5
    cbs
    dsmmsubg.p
    fveq2i
    3sstr4g
    #
    wph
    cP
    cR
    cS
    cH
    cI
    cV
    cW
    @2
    dsmmsubg.p
    dsmmsubg.h
    dsmmsubg.i
    dsmmsubg.s
    wph
    @17
    cgrp
    cmnd
    wss
    cI
    cmnd
    cR
    wf
    #
    dsmmsubg.r
    va
    cgrp
    cmnd
    @9
    grpmnd
    ssriv
    cI
    cgrp
    cmnd
    cR
    fss
    sylancl
    #
    @2
    eqid
    dsmm0cl
    wph
    @9
    cH
    wcel
    #
    @8
    cH
    wcel
    #
    w3a
    cP
    @0
    cR
    cS
    cH
    cI
    @9
    @8
    cV
    cW
    dsmmsubg.p
    dsmmsubg.h
    wph
    @22
    @18
    @23
    dsmmsubg.i
    3ad2ant1
    wph
    @22
    cS
    cV
    wcel
    #
    @23
    dsmmsubg.s
    3ad2ant1
    wph
    @22
    @20
    @23
    @21
    3ad2ant1
    wph
    @22
    @23
    simp2
    wph
    @22
    @23
    simp3
    @0
    eqid
    dsmmacl
    wph
    @22
    wa
    #
    @9
    cP
    cminusg
    cfv
    #
    cfv
    #
    cH
    wcel
    @27
    @7
    wcel
    #
    @8
    @27
    cfv
    #
    @12
    wne
    #
    vb
    cI
    crab
    #
    cfn
    wcel
    #
    @25
    cP
    cgrp
    wcel
    #
    @9
    @7
    wcel
    #
    @28
    wph
    @33
    @22
    wph
    cR
    cS
    cI
    cV
    cW
    cP
    dsmmsubg.p
    dsmmsubg.i
    dsmmsubg.s
    dsmmsubg.r
    prdsgrpd
    #
    adantr
    wph
    cH
    @7
    @9
    @19
    sselda
    #
    @7
    cP
    @26
    @9
    @7
    eqid
    #
    @26
    eqid
    #
    grpinvcl
    syl2anc
    @25
    @13
    vb
    cI
    crab
    #
    cfn
    wcel
    #
    @31
    @39
    wss
    @32
    @25
    @34
    @40
    @25
    @22
    @34
    @40
    wa
    wph
    @22
    simpr
    @25
    @7
    @3
    cP
    cR
    cS
    cH
    cI
    cW
    @9
    vb
    dsmmsubg.p
    @3
    eqid
    #
    @37
    dsmmsubg.h
    wph
    @18
    @22
    dsmmsubg.i
    adantr
    #
    wph
    cR
    cI
    wfn
    #
    @22
    wph
    @17
    @43
    dsmmsubg.r
    cI
    cgrp
    cR
    ffn
    syl
    adantr
    #
    dsmmelbas
    mpbid
    simprd
    @25
    @30
    @13
    vb
    cI
    @25
    @8
    cI
    wcel
    #
    wa
    #
    @10
    @12
    @29
    @12
    @25
    @45
    @10
    @12
    wceq
    #
    @29
    @12
    wceq
    @25
    @45
    @47
    wa
    wa
    @29
    @10
    @11
    cminusg
    cfv
    #
    cfv
    #
    @12
    @48
    cfv
    #
    @12
    @25
    @45
    @29
    @49
    wceq
    @47
    @46
    @7
    cR
    cS
    cI
    @8
    @26
    cV
    cW
    @9
    cP
    dsmmsubg.p
    wph
    @18
    @22
    @45
    dsmmsubg.i
    ad2antrr
    wph
    @24
    @22
    @45
    dsmmsubg.s
    ad2antrr
    wph
    @17
    @22
    @45
    dsmmsubg.r
    ad2antrr
    @37
    @38
    @25
    @34
    @45
    @36
    adantr
    @25
    @45
    simpr
    prdsinvgd2
    adantrr
    @47
    @49
    @50
    wceq
    @25
    @45
    @10
    @12
    @48
    fveq2
    ad2antll
    @25
    @45
    @50
    @12
    wceq
    #
    @47
    @46
    @11
    cgrp
    wcel
    #
    @51
    wph
    @45
    @52
    @22
    wph
    cI
    cgrp
    @8
    cR
    dsmmsubg.r
    ffvelrnda
    adantlr
    @11
    @48
    @12
    @12
    eqid
    @48
    eqid
    grpinvid
    syl
    adantrr
    3eqtrd
    expr
    necon3d
    ss2rabdv
    @39
    @31
    ssfi
    syl2anc
    @25
    @7
    @3
    cP
    cR
    cS
    cH
    cI
    cW
    @27
    vb
    dsmmsubg.p
    @41
    @37
    dsmmsubg.h
    @42
    @44
    dsmmelbas
    mpbir2and
    @35
    issubgrpd2
end
