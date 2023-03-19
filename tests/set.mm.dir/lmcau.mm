include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "clm.mm"
include "cdm.mm"
include "cca.mm"
include "cv.mm"
include "wbr.mm"
include "cha.mm"
include "wfun.mm"
include "wb.mm"
include "methaus.mm"
include "lmfun.mm"
include "funfvbrb.mm"
include "3syl.mm"
include "wa.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "cuz.mm"
include "cbl.mm"
include "cres.mm"
include "wf.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "wral.mm"
include "crn.mm"
include "w3a.mm"
include "id.mm"
include "lmmbr.mm"
include "biimpa.mm"
include "simp1d.mm"
include "c2.mm"
include "cdiv.mm"
include "simprr.mm"
include "cr.mm"
include "wss.mm"
include "simplll.mm"
include "simp2d.mm"
include "ad2antrr.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "wceq.mm"
include "uzid.mm"
include "ad2antrl.mm"
include "fvres.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "blhalf.mm"
include "syl22anc.mm"
include "fssd.mm"
include "rphalfcl.mm"
include "simp3d.mm"
include "oveq2.mm"
include "feq3d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "syl2im.mm"
include "impcom.mm"
include "cpw.mm"
include "wfn.mm"
include "uzf.mm"
include "ffn.mm"
include "reseq2.mm"
include "feq12d.mm"
include "rexrn.mm"
include "mp2b.mm"
include "sylib.mm"
include "reximddv.mm"
include "ralrimiva.mm"
include "iscau.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "ex.mm"
include "sylbid.mm"
include "ssrdv.mm"

theorem lmcau
  let cD: class D
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vj: setvar j
  let vu: setvar u
  let cF: class F
  assume lmcau.1: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> dom ( ~~>t ` J ) C_ ( Cau ` D ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    vf
    cJ
    clm
    cfv
    #
    cdm
    #
    cD
    cca
    cfv
    #
    @0
    vf
    cv
    #
    @2
    wcel
    #
    @4
    @4
    @1
    cfv
    #
    @1
    wbr
    #
    @4
    @3
    wcel
    #
    @0
    cJ
    cha
    wcel
    @1
    wfun
    @5
    @7
    wb
    cD
    cJ
    cX
    lmcau.1
    methaus
    cJ
    lmfun
    @4
    @1
    funfvbrb
    3syl
    @0
    @7
    @8
    @0
    @7
    wa
    #
    @8
    @4
    cX
    cc
    cpm
    co
    wcel
    #
    vj
    cv
    #
    cuz
    cfv
    #
    @11
    @4
    cfv
    #
    vx
    cv
    #
    cD
    cbl
    cfv
    #
    co
    #
    @4
    @12
    cres
    #
    wf
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    @9
    @10
    @6
    cX
    wcel
    #
    vu
    cv
    #
    @6
    vy
    cv
    #
    @15
    co
    #
    @4
    @22
    cres
    #
    wf
    #
    vu
    cuz
    crn
    #
    wrex
    #
    vy
    crp
    wral
    #
    @0
    @7
    @10
    @21
    @29
    w3a
    @0
    vy
    vu
    cD
    @6
    @4
    cJ
    cX
    lmcau.1
    @0
    id
    lmmbr
    biimpa
    #
    simp1d
    @9
    @19
    vx
    crp
    @9
    @14
    crp
    wcel
    #
    wa
    #
    @12
    @6
    @14
    c2
    cdiv
    co
    #
    @15
    co
    #
    @17
    wf
    #
    @18
    vj
    cz
    @32
    @11
    cz
    wcel
    #
    @35
    wa
    #
    wa
    #
    @12
    @34
    @16
    @17
    @32
    @36
    @35
    simprr
    #
    @38
    @0
    @21
    @14
    cr
    wcel
    #
    @13
    @34
    wcel
    @34
    @16
    wss
    @0
    @7
    @31
    @37
    simplll
    @9
    @21
    @31
    @37
    @9
    @10
    @21
    @29
    @30
    simp2d
    ad2antrr
    @31
    @40
    @9
    @37
    @14
    rpre
    ad2antlr
    @38
    @11
    @17
    cfv
    #
    @13
    @34
    @38
    @11
    @12
    wcel
    #
    @41
    @13
    wceq
    @36
    @42
    @32
    @35
    @11
    uzid
    ad2antrl
    #
    @11
    @12
    @4
    fvres
    syl
    @38
    @12
    @34
    @11
    @17
    @39
    @43
    ffvelrnd
    eqeltrrd
    @14
    cD
    cX
    @6
    @13
    blhalf
    syl22anc
    fssd
    @32
    @22
    @34
    @25
    wf
    #
    vu
    @27
    wrex
    #
    @35
    vj
    cz
    wrex
    #
    @31
    @9
    @45
    @31
    @33
    crp
    wcel
    @9
    @29
    @45
    @14
    rphalfcl
    @9
    @10
    @21
    @29
    @30
    simp3d
    @28
    @45
    vy
    @33
    crp
    @23
    @33
    wceq
    #
    @26
    @44
    vu
    @27
    @47
    @24
    @34
    @25
    @22
    @23
    @33
    @6
    @15
    oveq2
    feq3d
    rexbidv
    rspcv
    syl2im
    impcom
    cz
    cz
    cpw
    #
    cuz
    wf
    cuz
    cz
    wfn
    @45
    @46
    wb
    uzf
    cz
    @48
    cuz
    ffn
    @44
    @35
    vu
    vj
    cz
    cuz
    @22
    @12
    wceq
    #
    @22
    @12
    @34
    @25
    @17
    @22
    @12
    @4
    reseq2
    @49
    id
    feq12d
    rexrn
    mp2b
    sylib
    reximddv
    ralrimiva
    @0
    @8
    @10
    @20
    wa
    wb
    @7
    vx
    cD
    vj
    @4
    cX
    iscau
    adantr
    mpbir2and
    ex
    sylbid
    ssrdv
end
