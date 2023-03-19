include "cr.mm"
include "crp.mm"
include "ce.mm"
include "cres.mm"
include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "reeff1.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "wf.mm"
include "f1f.mm"
include "ffn.mm"
include "mp2b.mm"
include "wss.mm"
include "frn.mm"
include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "wrex.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "co.mm"
include "cc0.mm"
include "wa.mm"
include "wb.mm"
include "elrp.mm"
include "reclt1.mm"
include "sylbi.mm"
include "cneg.mm"
include "rpre.mm"
include "rpne0.mm"
include "rereccld.mm"
include "reeff1olem.mm"
include "sylan.mm"
include "wi.mm"
include "eqcom.mm"
include "cc.mm"
include "wne.mm"
include "rpcnne0.mm"
include "recn.mm"
include "efcl.mm"
include "syl.mm"
include "efne0.mm"
include "jca.mm"
include "rec11r.mm"
include "syl2an.mm"
include "cmul.mm"
include "efcan.mm"
include "eqcomd.mm"
include "negcl.mm"
include "ax-1cn.mm"
include "divmul2.mm"
include "mp3an1.mm"
include "syl12anc.mm"
include "mpbird.mm"
include "eqeq1d.mm"
include "adantl.mm"
include "bitrd.mm"
include "syl5bbr.mm"
include "biimpd.mm"
include "reximdva.mm"
include "adantr.mm"
include "mpd.mm"
include "renegcl.mm"
include "infm3lem.mm"
include "fveq2.mm"
include "rexxfr.mm"
include "sylibr.mm"
include "ex.mm"
include "sylbid.mm"
include "imp.mm"
include "ef0.mm"
include "eqeq2i.mm"
include "0re.mm"
include "rspcev.mm"
include "mpan.mm"
include "eqcoms.mm"
include "sylbir.mm"
include "w3o.mm"
include "1re.mm"
include "lttri4.mm"
include "sylancl.mm"
include "mpjao3dan.mm"
include "fvres.mm"
include "rexbiia.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "ssriv.mm"
include "eqssi.mm"
include "df-fo.mm"
include "mpbir2an.mm"
include "df-f1o.mm"

theorem reeff1o
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( exp |` RR ) : RR -1-1-onto-> RR+

  proof
    cr
    crp
    ce
    cr
    cres
    #
    wf1o
    cr
    crp
    @0
    wf1
    #
    cr
    crp
    @0
    wfo
    #
    reeff1
    @2
    @0
    cr
    wfn
    #
    @0
    crn
    #
    crp
    wceq
    @1
    cr
    crp
    @0
    wf
    #
    @3
    reeff1
    cr
    crp
    @0
    f1f
    #
    cr
    crp
    @0
    ffn
    mp2b
    #
    @4
    crp
    @1
    @5
    @4
    crp
    wss
    reeff1
    @6
    cr
    crp
    @0
    frn
    mp2b
    vz
    crp
    @4
    vz
    cv
    #
    crp
    wcel
    #
    vx
    cv
    #
    @0
    cfv
    #
    @8
    wceq
    #
    vx
    cr
    wrex
    #
    @8
    @4
    wcel
    #
    @9
    @10
    ce
    cfv
    #
    @8
    wceq
    #
    vx
    cr
    wrex
    #
    @13
    @9
    @8
    c1
    clt
    wbr
    #
    @17
    @8
    c1
    wceq
    #
    c1
    @8
    clt
    wbr
    #
    @9
    @18
    @17
    @9
    @18
    c1
    c1
    @8
    cdiv
    co
    #
    clt
    wbr
    #
    @17
    @9
    @8
    cr
    wcel
    #
    cc0
    @8
    clt
    wbr
    wa
    @18
    @22
    wb
    @8
    elrp
    @8
    reclt1
    sylbi
    @9
    @22
    @17
    @9
    @22
    wa
    #
    vy
    cv
    #
    cneg
    #
    ce
    cfv
    #
    @8
    wceq
    #
    vy
    cr
    wrex
    #
    @17
    @24
    @25
    ce
    cfv
    #
    @21
    wceq
    #
    vy
    cr
    wrex
    #
    @29
    @9
    @21
    cr
    wcel
    @22
    @32
    @9
    @8
    @8
    rpre
    #
    @8
    rpne0
    rereccld
    vy
    @21
    reeff1olem
    sylan
    @9
    @32
    @29
    wi
    @22
    @9
    @31
    @28
    vy
    cr
    @9
    @25
    cr
    wcel
    #
    wa
    #
    @31
    @28
    @31
    @21
    @30
    wceq
    #
    @35
    @28
    @21
    @30
    eqcom
    @35
    @36
    c1
    @30
    cdiv
    co
    #
    @8
    wceq
    #
    @28
    @9
    @8
    cc
    wcel
    @8
    cc0
    wne
    wa
    @30
    cc
    wcel
    #
    @30
    cc0
    wne
    #
    wa
    #
    @36
    @38
    wb
    @34
    @8
    rpcnne0
    @34
    @39
    @40
    @34
    @25
    cc
    wcel
    #
    @39
    @25
    recn
    #
    @25
    efcl
    #
    syl
    @34
    @42
    @40
    @43
    @25
    efne0
    #
    syl
    jca
    @8
    @30
    rec11r
    syl2an
    @34
    @38
    @28
    wb
    @9
    @34
    @37
    @27
    @8
    @34
    @42
    @37
    @27
    wceq
    #
    @43
    @42
    @46
    c1
    @30
    @27
    cmul
    co
    #
    wceq
    #
    @42
    @47
    c1
    @25
    efcan
    eqcomd
    @42
    @27
    cc
    wcel
    #
    @39
    @40
    @46
    @48
    wb
    #
    @42
    @26
    cc
    wcel
    @49
    @25
    negcl
    @26
    efcl
    syl
    @44
    @45
    c1
    cc
    wcel
    @49
    @41
    @50
    ax-1cn
    c1
    @27
    @30
    divmul2
    mp3an1
    syl12anc
    mpbird
    syl
    eqeq1d
    adantl
    bitrd
    syl5bbr
    biimpd
    reximdva
    adantr
    mpd
    @16
    @28
    vx
    vy
    @26
    cr
    cr
    @25
    renegcl
    vx
    vy
    infm3lem
    @10
    @26
    wceq
    @15
    @27
    @8
    @10
    @26
    ce
    fveq2
    eqeq1d
    rexxfr
    sylibr
    ex
    sylbid
    imp
    @19
    @17
    @9
    @19
    @8
    cc0
    ce
    cfv
    #
    wceq
    @17
    @51
    c1
    @8
    ef0
    eqeq2i
    @17
    @51
    @8
    cc0
    cr
    wcel
    @51
    @8
    wceq
    #
    @17
    0re
    @16
    @52
    vx
    cc0
    cr
    @10
    cc0
    wceq
    @15
    @51
    @8
    @10
    cc0
    ce
    fveq2
    eqeq1d
    rspcev
    mpan
    eqcoms
    sylbir
    adantl
    @9
    @23
    @20
    @17
    @33
    vx
    @8
    reeff1olem
    sylan
    @9
    @23
    c1
    cr
    wcel
    @18
    @19
    @20
    w3o
    @33
    1re
    @8
    c1
    lttri4
    sylancl
    mpjao3dan
    @12
    @16
    vx
    cr
    @10
    cr
    wcel
    @11
    @15
    @8
    @10
    cr
    ce
    fvres
    eqeq1d
    rexbiia
    sylibr
    @3
    @14
    @13
    wb
    @7
    vx
    cr
    @8
    @0
    fvelrnb
    ax-mp
    sylibr
    ssriv
    eqssi
    cr
    crp
    @0
    df-fo
    mpbir2an
    cr
    crp
    @0
    df-f1o
    mpbir2an
end
