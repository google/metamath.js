include "c1stc.mm"
include "wcel.mm"
include "ctop.mm"
include "ckgen.mm"
include "cfv.mm"
include "wss.mm"
include "crn.mm"
include "1stctop.mm"
include "cv.mm"
include "wa.mm"
include "cuni.mm"
include "cdif.mm"
include "ccld.mm"
include "ccl.mm"
include "cn.mm"
include "wf.mm"
include "clm.mm"
include "wbr.mm"
include "wex.mm"
include "wb.mm"
include "difss.mm"
include "eqid.mm"
include "1stcelcls.mm"
include "mpan2.mm"
include "adantr.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "simprr.mm"
include "lmcl.mm"
include "syl2anc.mm"
include "csn.mm"
include "cun.mm"
include "crest.mm"
include "co.mm"
include "c1.mm"
include "nnuz.mm"
include "cvv.mm"
include "vex.mm"
include "rnex.mm"
include "snex.mm"
include "unex.mm"
include "resttop.mm"
include "sylancl.mm"
include "1zzd.mm"
include "a1i.mm"
include "ssun2.mm"
include "snss.mm"
include "mpbir.mm"
include "wfn.mm"
include "ffn.mm"
include "ad2antrl.mm"
include "dffn3.mm"
include "ssun1.mm"
include "fss.mm"
include "lmss.mm"
include "mpbid.mm"
include "ffvelrnda.mm"
include "simprl.mm"
include "eldifbd.mm"
include "eldifd.mm"
include "cin.mm"
include "difin.mm"
include "wceq.mm"
include "frn.mm"
include "difss2d.mm"
include "snssd.mm"
include "unssd.mm"
include "restuni.mm"
include "difeq1d.mm"
include "syl5eqr.mm"
include "incom.mm"
include "ccmp.mm"
include "simplr.mm"
include "1stckgenlem.mm"
include "kgeni.mm"
include "syl5eqel.mm"
include "opncld.mm"
include "eqeltrd.mm"
include "lmcld.mm"
include "ex.mm"
include "exlimdv.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "iscld4.mm"
include "mpbird.mm"
include "elssuni.mm"
include "adantl.mm"
include "kgenuni.mm"
include "syl.mm"
include "sseqtr4d.mm"
include "isopn2.mm"
include "iskgen2.mm"
include "sylanbrc.mm"

theorem 1stckgen
  let cJ: class J
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let wph: wff ph


  assert |- ( J e. 1stc -> J e. ran kGen )

  proof
    cJ
    c1stc
    wcel
    #
    cJ
    ctop
    wcel
    #
    cJ
    ckgen
    cfv
    #
    cJ
    wss
    cJ
    ckgen
    crn
    wcel
    cJ
    1stctop
    #
    @0
    vx
    @2
    cJ
    @0
    vx
    cv
    #
    @2
    wcel
    #
    @4
    cJ
    wcel
    #
    @0
    @5
    wa
    #
    @6
    cJ
    cuni
    #
    @4
    cdif
    #
    cJ
    ccld
    cfv
    wcel
    #
    @7
    @10
    @9
    cJ
    ccl
    cfv
    cfv
    #
    @9
    wss
    #
    @7
    vy
    @11
    @9
    @7
    vy
    cv
    #
    @11
    wcel
    #
    cn
    @9
    vf
    cv
    #
    wf
    #
    @15
    @13
    cJ
    clm
    cfv
    wbr
    #
    wa
    #
    vf
    wex
    #
    @13
    @9
    wcel
    #
    @0
    @14
    @19
    wb
    #
    @5
    @0
    @9
    @8
    wss
    #
    @21
    @8
    @4
    difss
    #
    @13
    @9
    vf
    cJ
    @8
    @8
    eqid
    #
    1stcelcls
    mpan2
    adantr
    @7
    @18
    @20
    vf
    @7
    @18
    @20
    @7
    @18
    wa
    #
    @13
    @8
    @4
    @25
    cJ
    @8
    ctopon
    cfv
    wcel
    #
    @17
    @13
    @8
    wcel
    @25
    @1
    @26
    @7
    @1
    @18
    @0
    @1
    @5
    @3
    adantr
    #
    adantr
    #
    cJ
    @8
    @24
    toptopon
    sylib
    #
    @7
    @16
    @17
    simprr
    #
    @13
    @15
    cJ
    @8
    lmcl
    syl2anc
    #
    @25
    @13
    @15
    crn
    #
    @13
    csn
    #
    cun
    #
    @4
    @25
    @13
    @34
    @4
    cdif
    #
    vk
    @15
    cJ
    @34
    crest
    co
    #
    c1
    @36
    cuni
    #
    cn
    nnuz
    @25
    @36
    ctop
    wcel
    #
    @36
    @37
    ctopon
    cfv
    wcel
    @25
    @1
    @34
    cvv
    wcel
    #
    @38
    @28
    @32
    @33
    @15
    vf
    vex
    rnex
    @13
    snex
    unex
    #
    @34
    cJ
    cvv
    resttop
    sylancl
    #
    @36
    @37
    @37
    eqid
    #
    toptopon
    sylib
    @25
    1zzd
    #
    @25
    @17
    @15
    @13
    @36
    clm
    cfv
    wbr
    @30
    @25
    @13
    @15
    cJ
    @36
    c1
    cvv
    @34
    cn
    @36
    eqid
    nnuz
    @39
    @25
    @40
    a1i
    @28
    @13
    @34
    wcel
    #
    @25
    @44
    @33
    @34
    wss
    @33
    @32
    ssun2
    @13
    @34
    vy
    vex
    snss
    mpbir
    a1i
    @43
    @25
    cn
    @32
    @15
    wf
    #
    @32
    @34
    wss
    cn
    @34
    @15
    wf
    @25
    @15
    cn
    wfn
    #
    @45
    @16
    @46
    @7
    @17
    cn
    @9
    @15
    ffn
    ad2antrl
    cn
    @15
    dffn3
    sylib
    @32
    @33
    ssun1
    cn
    @32
    @34
    @15
    fss
    sylancl
    #
    lmss
    mpbid
    @25
    vk
    cv
    #
    cn
    wcel
    wa
    #
    @48
    @15
    cfv
    #
    @34
    @4
    @25
    cn
    @34
    @48
    @15
    @47
    ffvelrnda
    @49
    @50
    @8
    @4
    @25
    cn
    @9
    @48
    @15
    @7
    @16
    @17
    simprl
    #
    ffvelrnda
    eldifbd
    eldifd
    @25
    @35
    @37
    @34
    @4
    cin
    #
    cdif
    #
    @36
    ccld
    cfv
    #
    @25
    @35
    @34
    @52
    cdif
    @53
    @34
    @4
    difin
    @25
    @34
    @37
    @52
    @25
    @1
    @34
    @8
    wss
    @34
    @37
    wceq
    @28
    @25
    @32
    @33
    @8
    @25
    @32
    @8
    @4
    @16
    @32
    @9
    wss
    @7
    @17
    cn
    @9
    @15
    frn
    ad2antrl
    difss2d
    @25
    @13
    @8
    @31
    snssd
    unssd
    @34
    cJ
    @8
    @24
    restuni
    syl2anc
    difeq1d
    syl5eqr
    @25
    @38
    @52
    @36
    wcel
    @53
    @54
    wcel
    @41
    @25
    @52
    @4
    @34
    cin
    #
    @36
    @34
    @4
    incom
    @25
    @5
    @36
    ccmp
    wcel
    @55
    @36
    wcel
    @0
    @5
    @18
    simplr
    @25
    @13
    @15
    cJ
    @8
    @29
    @25
    @16
    @22
    cn
    @8
    @15
    wf
    @51
    @23
    cn
    @9
    @8
    @15
    fss
    sylancl
    @30
    1stckgenlem
    @4
    cJ
    @34
    kgeni
    syl2anc
    syl5eqel
    @52
    @36
    @37
    @42
    opncld
    syl2anc
    eqeltrd
    lmcld
    eldifbd
    eldifd
    ex
    exlimdv
    sylbid
    ssrdv
    @7
    @1
    @22
    @10
    @12
    wb
    @27
    @23
    @9
    cJ
    @8
    @24
    iscld4
    sylancl
    mpbird
    @7
    @1
    @4
    @8
    wss
    @6
    @10
    wb
    @27
    @7
    @4
    @2
    cuni
    #
    @8
    @5
    @4
    @56
    wss
    @0
    @4
    @2
    elssuni
    adantl
    @7
    @1
    @8
    @56
    wceq
    @27
    cJ
    @8
    @24
    kgenuni
    syl
    sseqtr4d
    @4
    cJ
    @8
    @24
    isopn2
    syl2anc
    mpbird
    ex
    ssrdv
    cJ
    iskgen2
    sylanbrc
end
