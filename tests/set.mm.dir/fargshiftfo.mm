include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cdm.mm"
include "wfo.mm"
include "wa.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "wf.mm"
include "crn.mm"
include "wceq.mm"
include "fof.mm"
include "fargshiftf.mm"
include "sylan2.mm"
include "cv.mm"
include "caddc.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt.mm"
include "wfn.mm"
include "fofn.mm"
include "fnrnfv.mm"
include "syl.mm"
include "adantl.mm"
include "wi.mm"
include "df-fo.mm"
include "biimpi.mm"
include "eqeq1.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "wb.mm"
include "ffn.mm"
include "fseq1hash.mm"
include "fz0add1fz1.mm"
include "cmin.mm"
include "cz.mm"
include "nn0z.mm"
include "fzval3.mm"
include "nn0cn.mm"
include "1cnd.mm"
include "addcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "adantr.mm"
include "fzosubel3.mm"
include "syl2anc.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "cc.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "npcand.mm"
include "eqcomd.mm"
include "rspcedvd.mm"
include "fveq2.mm"
include "rexxfrd.mm"
include "oveq2.mm"
include "rexeqdv.mm"
include "bibi2d.mm"
include "mpbird.mm"
include "syldan.mm"
include "abbidv.mm"
include "eqeq1d.mm"
include "biimpcd.mm"
include "syl6bi.mm"
include "com23.mm"
include "mpcom.mm"
include "mpd.mm"
include "syl5eq.mm"
include "dffo2.mm"
include "sylanbrc.mm"

theorem fargshiftfo
  let vx: setvar x
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vl: setvar l
  let vy: setvar y
  let vz: setvar z
  assume fargshift.g: |- G = ( x e. ( 0 ..^ ( # ` F ) ) |-> ( F ` ( x + 1 ) ) )

  disjoint F x
  disjoint E x
  disjoint N x
  disjoint X x
  disjoint F k
  disjoint F l
  disjoint F y
  disjoint F z
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint l x
  disjoint l y
  disjoint l z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint E y
  disjoint E z
  disjoint G y
  disjoint G z
  disjoint N y
  disjoint N z
  disjoint k x
  assert |- ( ( N e. NN0 /\ F : ( 1 ... N ) -onto-> dom E ) -> G : ( 0 ..^ ( # ` F ) ) -onto-> dom E )

  proof
    cN
    cn0
    wcel
    #
    c1
    cN
    cfz
    co
    #
    cE
    cdm
    #
    cF
    wfo
    #
    wa
    #
    cc0
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    @2
    cG
    wf
    #
    cG
    crn
    #
    @2
    wceq
    @6
    @2
    cG
    wfo
    @3
    @0
    @1
    @2
    cF
    wf
    #
    @7
    @1
    @2
    cF
    fof
    #
    vx
    cE
    cF
    cG
    cN
    fargshift.g
    fargshiftf
    sylan2
    @4
    @8
    vy
    cv
    #
    vx
    cv
    #
    c1
    caddc
    co
    #
    cF
    cfv
    #
    wceq
    #
    vx
    @6
    wrex
    #
    vy
    cab
    #
    @2
    vx
    vy
    @6
    @14
    cG
    fargshift.g
    rnmpt
    @4
    cF
    crn
    #
    @11
    vz
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vz
    @1
    wrex
    #
    vy
    cab
    #
    wceq
    #
    @17
    @2
    wceq
    #
    @3
    @24
    @0
    @3
    cF
    @1
    wfn
    #
    @24
    @1
    @2
    cF
    fofn
    vz
    vy
    @1
    cF
    fnrnfv
    syl
    adantl
    @26
    @18
    @2
    wceq
    #
    wa
    #
    @4
    @24
    @25
    wi
    #
    @3
    @28
    @0
    @3
    @28
    @1
    @2
    cF
    df-fo
    biimpi
    adantl
    @27
    @4
    @29
    wi
    @26
    @27
    @24
    @4
    @25
    @27
    @24
    @23
    @2
    wceq
    #
    @4
    @25
    wi
    @27
    @24
    @2
    @23
    wceq
    @30
    @18
    @2
    @23
    eqeq1
    @2
    @23
    eqcom
    syl6bb
    @4
    @30
    @25
    @4
    @23
    @17
    @2
    @4
    @22
    @16
    vy
    @0
    @3
    @5
    cN
    wceq
    #
    @22
    @16
    wb
    #
    @3
    @0
    @9
    @31
    @10
    @9
    @0
    @26
    @31
    @1
    @2
    cF
    ffn
    cF
    cN
    fseq1hash
    sylan2
    sylan2
    @0
    @31
    wa
    @32
    @22
    @15
    vx
    cc0
    cN
    cfzo
    co
    #
    wrex
    #
    wb
    #
    @0
    @35
    @31
    @0
    @21
    @15
    vz
    vx
    @13
    @1
    @33
    cN
    @12
    fz0add1fz1
    @0
    @19
    @1
    wcel
    #
    wa
    #
    @19
    @13
    wceq
    #
    @19
    @19
    c1
    cmin
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vx
    @39
    @33
    @37
    @19
    c1
    c1
    cN
    caddc
    co
    #
    cfzo
    co
    #
    wcel
    #
    cN
    cz
    wcel
    #
    @39
    @33
    wcel
    @0
    @36
    @44
    @0
    @1
    @43
    @19
    @0
    @1
    c1
    cN
    c1
    caddc
    co
    #
    cfzo
    co
    #
    @43
    @0
    @45
    @1
    @47
    wceq
    cN
    nn0z
    #
    c1
    cN
    fzval3
    syl
    @0
    @46
    @42
    c1
    cfzo
    @0
    cN
    c1
    cN
    nn0cn
    @0
    1cnd
    addcomd
    oveq2d
    eqtrd
    eleq2d
    biimpa
    @0
    @45
    @36
    @48
    adantr
    @19
    c1
    cN
    fzosubel3
    syl2anc
    @12
    @39
    wceq
    #
    @38
    @41
    wb
    @37
    @49
    @13
    @40
    @19
    @12
    @39
    c1
    caddc
    oveq1
    eqeq2d
    adantl
    @37
    @40
    @19
    @37
    @19
    c1
    @36
    @19
    cc
    wcel
    @0
    @36
    @19
    @19
    c1
    cN
    elfzelz
    zcnd
    adantl
    @37
    1cnd
    npcand
    eqcomd
    rspcedvd
    @38
    @21
    @15
    wb
    @0
    @38
    @20
    @14
    @11
    @19
    @13
    cF
    fveq2
    eqeq2d
    adantl
    rexxfrd
    adantr
    @31
    @32
    @35
    wb
    @0
    @31
    @16
    @34
    @22
    @31
    @15
    vx
    @6
    @33
    @5
    cN
    cc0
    cfzo
    oveq2
    rexeqdv
    bibi2d
    adantl
    mpbird
    syldan
    abbidv
    eqeq1d
    biimpcd
    syl6bi
    com23
    adantl
    mpcom
    mpd
    syl5eq
    @6
    @2
    cG
    dffo2
    sylanbrc
end
