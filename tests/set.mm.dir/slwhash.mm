include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cpc.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "csubg.mm"
include "wcel.mm"
include "cgrp.mm"
include "cslw.mm"
include "slwsubg.mm"
include "syl.mm"
include "subgrcl.mm"
include "cprime.mm"
include "slwprm.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "grpbn0.mm"
include "cfn.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "pccld.mm"
include "cdvds.mm"
include "wbr.mm"
include "pcdvds.mm"
include "syl2anc.mm"
include "sylow1.mm"
include "wa.mm"
include "cplusg.mm"
include "csg.mm"
include "cmpt.mm"
include "crn.mm"
include "wss.mm"
include "adantr.mm"
include "simprl.mm"
include "eqid.mm"
include "cress.mm"
include "cpgp.mm"
include "slwpgp.mm"
include "simprr.mm"
include "sylow2b.mm"
include "cbs.mm"
include "cn0.mm"
include "wrex.mm"
include "ad2antrr.mm"
include "conjsubg.mm"
include "subgbas.mm"
include "fveq2d.mm"
include "cen.mm"
include "conjsubgen.mm"
include "subgss.mm"
include "ssfi.mm"
include "hashen.mm"
include "simplrr.mm"
include "eqtr3d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "subggrp.mm"
include "eqeltrrd.mm"
include "pgpfi.mm"
include "mpbir2and.mm"
include "slwispgp.mm"
include "mpbi2and.mm"
include "eqtrd.mm"
include "rexlimddv.mm"

theorem slwhash
  let wph: wff ph
  let cP: class P
  let cG: class G
  let cH: class H
  let cX: class X
  let vg: setvar g
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vp: setvar p
  assume fislw.1: |- X = ( Base ` G )
  assume slwhash.3: |- ( ph -> X e. Fin )
  assume slwhash.4: |- ( ph -> H e. ( P pSyl G ) )


  assert |- ( ph -> ( # ` H ) = ( P ^ ( P pCnt ( # ` X ) ) ) )

  proof
    wph
    vk
    cv
    #
    chash
    cfv
    #
    cP
    cP
    cX
    chash
    cfv
    #
    cpc
    co
    #
    cexp
    co
    #
    wceq
    #
    cH
    chash
    cfv
    #
    @4
    wceq
    #
    vk
    cG
    csubg
    cfv
    #
    wph
    cP
    vk
    cG
    @3
    cX
    fislw.1
    wph
    cH
    @8
    wcel
    #
    cG
    cgrp
    wcel
    #
    wph
    cH
    cP
    cG
    cslw
    co
    wcel
    #
    @9
    slwhash.4
    cP
    cG
    cH
    slwsubg
    syl
    #
    cH
    cG
    subgrcl
    syl
    #
    slwhash.3
    wph
    @11
    cP
    cprime
    wcel
    #
    slwhash.4
    cP
    cG
    cH
    slwprm
    #
    syl
    #
    wph
    cP
    @2
    @16
    wph
    @2
    cn
    wcel
    #
    cX
    c0
    wne
    #
    wph
    @10
    @18
    @13
    cX
    cG
    fislw.1
    grpbn0
    syl
    wph
    cX
    cfn
    wcel
    #
    @17
    @18
    wb
    slwhash.3
    cX
    hashnncl
    syl
    mpbird
    #
    pccld
    #
    wph
    @14
    @17
    @4
    @2
    cdvds
    wbr
    @16
    @20
    cP
    @2
    pcdvds
    syl2anc
    sylow1
    wph
    @0
    @8
    wcel
    #
    @5
    wa
    #
    wa
    #
    cH
    vx
    @0
    vg
    cv
    #
    vx
    cv
    cG
    cplusg
    cfv
    #
    co
    @25
    cG
    csg
    cfv
    #
    co
    cmpt
    #
    crn
    #
    wss
    #
    @7
    vg
    cX
    @24
    vx
    cP
    @26
    vg
    cG
    cH
    @0
    @27
    cX
    fislw.1
    wph
    @19
    @23
    slwhash.3
    adantr
    wph
    @9
    @23
    @12
    adantr
    wph
    @22
    @5
    simprl
    #
    @26
    eqid
    #
    wph
    cP
    cG
    cH
    cress
    co
    #
    cpgp
    wbr
    #
    @23
    wph
    @11
    @34
    slwhash.4
    cP
    @33
    cG
    cH
    @33
    eqid
    slwpgp
    syl
    adantr
    wph
    @22
    @5
    simprr
    @27
    eqid
    #
    sylow2b
    @24
    @25
    cX
    wcel
    #
    @30
    wa
    #
    wa
    #
    @6
    @29
    chash
    cfv
    #
    @4
    @38
    cH
    @29
    chash
    @38
    @30
    cP
    cG
    @29
    cress
    co
    #
    cpgp
    wbr
    #
    cH
    @29
    wceq
    #
    @24
    @36
    @30
    simprr
    @38
    @41
    @14
    @40
    cbs
    cfv
    #
    chash
    cfv
    #
    cP
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cn0
    wrex
    #
    @38
    @11
    @14
    wph
    @11
    @23
    @37
    slwhash.4
    ad2antrr
    #
    @15
    syl
    @38
    @3
    cn0
    wcel
    #
    @44
    @4
    wceq
    #
    @48
    wph
    @50
    @23
    @37
    @21
    ad2antrr
    @38
    @39
    @44
    @4
    @38
    @29
    @43
    chash
    @38
    @29
    @8
    wcel
    #
    @29
    @43
    wceq
    @38
    @22
    @36
    @52
    @24
    @22
    @37
    @31
    adantr
    #
    @24
    @36
    @30
    simprl
    #
    vx
    @25
    @26
    @0
    @28
    cG
    @27
    cX
    fislw.1
    @32
    @35
    @28
    eqid
    #
    conjsubg
    syl2anc
    #
    @29
    cG
    @40
    @40
    eqid
    #
    subgbas
    syl
    #
    fveq2d
    @38
    @1
    @39
    @4
    @38
    @1
    @39
    wceq
    #
    @0
    @29
    cen
    wbr
    #
    @38
    @22
    @36
    @60
    @53
    @54
    vx
    @25
    @26
    @0
    @28
    cG
    @27
    cX
    fislw.1
    @32
    @35
    @55
    conjsubgen
    syl2anc
    @38
    @0
    cfn
    wcel
    #
    @29
    cfn
    wcel
    #
    @59
    @60
    wb
    @38
    @19
    @0
    cX
    wss
    #
    @61
    wph
    @19
    @23
    @37
    slwhash.3
    ad2antrr
    #
    @38
    @22
    @63
    @53
    cX
    @0
    cG
    fislw.1
    subgss
    syl
    cX
    @0
    ssfi
    syl2anc
    @38
    @19
    @29
    cX
    wss
    #
    @62
    @64
    @38
    @52
    @65
    @56
    cX
    @29
    cG
    fislw.1
    subgss
    syl
    cX
    @29
    ssfi
    syl2anc
    #
    @0
    @29
    hashen
    syl2anc
    mpbird
    wph
    @22
    @5
    @37
    simplrr
    eqtr3d
    #
    eqtr3d
    @47
    @51
    vn
    @3
    cn0
    @45
    @3
    wceq
    @46
    @4
    @44
    @45
    @3
    cP
    cexp
    oveq2
    eqeq2d
    rspcev
    syl2anc
    @38
    @40
    cgrp
    wcel
    #
    @43
    cfn
    wcel
    @41
    @14
    @48
    wa
    wb
    @38
    @52
    @68
    @56
    @29
    cG
    @40
    @57
    subggrp
    syl
    @38
    @29
    @43
    cfn
    @58
    @66
    eqeltrrd
    cP
    vn
    @40
    @43
    @43
    eqid
    pgpfi
    syl2anc
    mpbir2and
    @38
    @11
    @52
    @30
    @41
    wa
    @42
    wb
    @49
    @56
    cP
    @40
    cG
    cH
    @29
    @57
    slwispgp
    syl2anc
    mpbi2and
    fveq2d
    @67
    eqtrd
    rexlimddv
    rexlimddv
end
