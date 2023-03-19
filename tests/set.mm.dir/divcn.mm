include "cdiv.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "c1.mm"
include "co.mm"
include "cmul.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "wceq.mm"
include "crio.mm"
include "df-div.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "eldifsn.mm"
include "w3a.mm"
include "divval.mm"
include "divrec.mm"
include "eqtr3d.mm"
include "3expb.mm"
include "sylan2b.mm"
include "mpt2eq3ia.mm"
include "eqtri.mm"
include "wtru.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "crest.mm"
include "wss.mm"
include "difss.mm"
include "resttopon.mm"
include "sylancl.mm"
include "syl5eqel.mm"
include "cnmpt1st.mm"
include "cnmpt2nd.mm"
include "cmpt.mm"
include "wf.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "eqid.mm"
include "reccl.mm"
include "sylbi.mm"
include "fmpti.mm"
include "cle.mm"
include "cif.mm"
include "c2.mm"
include "reccn2.mm"
include "wb.mm"
include "ovres.mm"
include "eldifi.mm"
include "cnmetdval.mm"
include "abssub.mm"
include "eqtrd.mm"
include "syl2an.mm"
include "breq1d.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "oveqan12d.mm"
include "imbi12d.mm"
include "ralbidva.mm"
include "rexbidv.mm"
include "adantr.mm"
include "mpbird.mm"
include "rgen2.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "xmetres2.mm"
include "mp2an.mm"
include "cmopn.mm"
include "cnfldtopn.mm"
include "metrest.mm"
include "metcn.mm"
include "mpbir2an.mm"
include "cnmpt21.mm"
include "mulcn.mm"
include "cnmpt22f.mm"
include "trud.mm"
include "eqeltri.mm"

theorem divcn
  let cJ: class J
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  assume addcn.j: |- J = ( TopOpen ` CCfld )
  assume divcn.k: |- K = ( J |`t ( CC \ { 0 } ) )


  assert |- / e. ( ( J tX K ) Cn J )

  proof
    cdiv
    vx
    vy
    cc
    cc
    cc0
    csn
    #
    cdif
    #
    vx
    cv
    #
    c1
    vy
    cv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cmpt2
    #
    cJ
    cK
    ctx
    co
    cJ
    ccn
    co
    #
    cdiv
    vx
    vy
    cc
    @1
    @3
    vz
    cv
    #
    cmul
    co
    @2
    wceq
    vz
    cc
    crio
    #
    cmpt2
    @6
    vx
    vy
    vz
    df-div
    vx
    vy
    cc
    @1
    @9
    @5
    @3
    @1
    wcel
    @2
    cc
    wcel
    #
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    #
    wa
    @9
    @5
    wceq
    #
    @3
    cc
    cc0
    eldifsn
    @10
    @11
    @12
    @13
    @10
    @11
    @12
    w3a
    @2
    @3
    cdiv
    co
    @9
    @5
    vz
    @2
    @3
    divval
    @2
    @3
    divrec
    eqtr3d
    3expb
    sylan2b
    mpt2eq3ia
    eqtri
    @6
    @7
    wcel
    wtru
    vx
    vy
    @2
    @4
    cmul
    cJ
    cK
    cJ
    cJ
    cJ
    cc
    @1
    cJ
    cc
    ctopon
    cfv
    wcel
    #
    wtru
    cJ
    addcn.j
    cnfldtopon
    a1i
    #
    wtru
    cK
    cJ
    @1
    crest
    co
    #
    @1
    ctopon
    cfv
    #
    divcn.k
    wtru
    @14
    @1
    cc
    wss
    #
    @16
    @17
    wcel
    @15
    cc
    @0
    difss
    #
    @1
    cJ
    cc
    resttopon
    sylancl
    syl5eqel
    #
    wtru
    vx
    vy
    cJ
    cK
    cc
    @1
    @15
    @20
    cnmpt1st
    wtru
    vx
    vy
    vz
    @3
    c1
    @8
    cdiv
    co
    #
    @4
    cJ
    cK
    cK
    cJ
    cc
    @1
    @1
    @15
    @20
    wtru
    vx
    vy
    cJ
    cK
    cc
    @1
    @15
    @20
    cnmpt2nd
    @20
    vz
    @1
    @21
    cmpt
    #
    cK
    cJ
    ccn
    co
    wcel
    #
    wtru
    @23
    @1
    cc
    @22
    wf
    #
    @2
    vw
    cv
    #
    cabs
    cmin
    ccom
    #
    @1
    @1
    cxp
    cres
    #
    co
    #
    vu
    cv
    #
    clt
    wbr
    #
    @2
    @22
    cfv
    #
    @25
    @22
    cfv
    #
    @26
    co
    #
    @3
    clt
    wbr
    #
    wi
    #
    vw
    @1
    wral
    #
    vu
    crp
    wrex
    #
    vy
    crp
    wral
    vx
    @1
    wral
    #
    vz
    @1
    cc
    @21
    @22
    @22
    eqid
    #
    @8
    @1
    wcel
    @8
    cc
    wcel
    @8
    cc0
    wne
    wa
    @21
    cc
    wcel
    @8
    cc
    cc0
    eldifsn
    @8
    reccl
    sylbi
    fmpti
    @37
    vx
    vy
    @1
    crp
    @2
    @1
    wcel
    #
    @3
    crp
    wcel
    #
    wa
    @37
    @25
    @2
    cmin
    co
    cabs
    cfv
    #
    @29
    clt
    wbr
    #
    c1
    @25
    cdiv
    co
    #
    c1
    @2
    cdiv
    co
    #
    cmin
    co
    cabs
    cfv
    #
    @3
    clt
    wbr
    #
    wi
    #
    vw
    @1
    wral
    #
    vu
    crp
    wrex
    #
    vu
    vw
    @2
    @3
    c1
    @2
    cabs
    cfv
    #
    @3
    cmul
    co
    #
    cle
    wbr
    c1
    @52
    cif
    @51
    c2
    cdiv
    co
    cmul
    co
    #
    @53
    eqid
    reccn2
    @40
    @37
    @50
    wb
    @41
    @40
    @36
    @49
    vu
    crp
    @40
    @35
    @48
    vw
    @1
    @40
    @25
    @1
    wcel
    #
    wa
    #
    @30
    @43
    @34
    @47
    @55
    @28
    @42
    @29
    clt
    @55
    @28
    @2
    @25
    @26
    co
    #
    @42
    @2
    @25
    @1
    @1
    @26
    ovres
    @40
    @10
    @25
    cc
    wcel
    #
    @56
    @42
    wceq
    @54
    @2
    cc
    @0
    eldifi
    @25
    cc
    @0
    eldifi
    @10
    @57
    wa
    @56
    @2
    @25
    cmin
    co
    cabs
    cfv
    @42
    @2
    @25
    @26
    @26
    eqid
    #
    cnmetdval
    @2
    @25
    abssub
    eqtrd
    syl2an
    eqtrd
    breq1d
    @55
    @33
    @46
    @3
    clt
    @55
    @33
    @45
    @44
    @26
    co
    #
    @46
    @40
    @54
    @31
    @45
    @32
    @44
    @26
    vz
    @2
    @21
    @45
    @1
    @22
    @8
    @2
    c1
    cdiv
    oveq2
    @39
    c1
    @2
    cdiv
    ovex
    fvmpt
    vz
    @25
    @21
    @44
    @1
    @22
    @8
    @25
    c1
    cdiv
    oveq2
    @39
    c1
    @25
    cdiv
    ovex
    fvmpt
    oveqan12d
    @40
    @45
    cc
    wcel
    #
    @44
    cc
    wcel
    #
    @59
    @46
    wceq
    @54
    @40
    @10
    @2
    cc0
    wne
    wa
    @60
    @2
    cc
    cc0
    eldifsn
    @2
    reccl
    sylbi
    @54
    @57
    @25
    cc0
    wne
    wa
    @61
    @25
    cc
    cc0
    eldifsn
    @25
    reccl
    sylbi
    @60
    @61
    wa
    @59
    @45
    @44
    cmin
    co
    cabs
    cfv
    @46
    @45
    @44
    @26
    @58
    cnmetdval
    @45
    @44
    abssub
    eqtrd
    syl2an
    eqtrd
    breq1d
    imbi12d
    ralbidva
    rexbidv
    adantr
    mpbird
    rgen2
    @27
    @1
    cxmt
    cfv
    wcel
    #
    @26
    cc
    cxmt
    cfv
    wcel
    #
    @23
    @24
    @38
    wa
    wb
    @63
    @18
    @62
    cnxmet
    @19
    @26
    @1
    cc
    xmetres2
    mp2an
    cnxmet
    vx
    vy
    vu
    vw
    @27
    @26
    @22
    cK
    cJ
    @1
    cc
    cK
    @16
    @27
    cmopn
    cfv
    #
    divcn.k
    @63
    @18
    @16
    @64
    wceq
    cnxmet
    @19
    @26
    @27
    cJ
    @64
    cc
    @1
    @27
    eqid
    cJ
    addcn.j
    cnfldtopn
    #
    @64
    eqid
    metrest
    mp2an
    eqtri
    @65
    metcn
    mp2an
    mpbir2an
    a1i
    @8
    @3
    c1
    cdiv
    oveq2
    cnmpt21
    cmul
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    wtru
    cJ
    addcn.j
    mulcn
    a1i
    cnmpt22f
    trud
    eqeltri
end
