include "cioo.mm"
include "cq.mm"
include "cxp.mm"
include "cima.mm"
include "ctg.mm"
include "cfv.mm"
include "crn.mm"
include "wss.mm"
include "wceq.mm"
include "imassrn.mm"
include "cxr.mm"
include "wf.mm"
include "wfn.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "cr.mm"
include "cpw.mm"
include "ioof.mm"
include "ffn.mm"
include "ax-mp.mm"
include "wa.mm"
include "wrex.mm"
include "clt.mm"
include "wbr.mm"
include "simpll.mm"
include "w3a.mm"
include "elioo1.mm"
include "biimpa.mm"
include "simp1d.mm"
include "simp2d.mm"
include "qbtwnxr.mm"
include "syl3anc.mm"
include "simplr.mm"
include "simp3d.mm"
include "reeanv.mm"
include "cop.mm"
include "df-ov.mm"
include "opelxpi.mm"
include "3ad2ant2.mm"
include "wfun.mm"
include "cdm.mm"
include "wi.mm"
include "ffun.mm"
include "qssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "xpss12.mm"
include "mp2an.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "funfvima2.mm"
include "syl.mm"
include "syl5eqel.mm"
include "3ad2ant1.mm"
include "simp3lr.mm"
include "simp3rl.mm"
include "wb.mm"
include "simp2l.mm"
include "sseldi.mm"
include "simp2r.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "cle.mm"
include "simp3ll.mm"
include "xrltle.mm"
include "mpd.mm"
include "iooss1.mm"
include "simp3rr.mm"
include "iooss2.mm"
include "sstrd.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "3exp.mm"
include "rexlimdvv.mm"
include "syl5bir.mm"
include "mp2and.mm"
include "ralrimiva.mm"
include "ctb.mm"
include "qtopbas.mm"
include "eltg2b.mm"
include "sylibr.mm"
include "rgen2a.mm"
include "ffnov.mm"
include "mpbir2an.mm"
include "frn.mm"
include "2basgen.mm"
include "eqtr2i.mm"

theorem tgqioo
  let cQ: class Q
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tgqioo.1: |- Q = ( topGen ` ( (,) " ( QQ X. QQ ) ) )


  assert |- ( topGen ` ran (,) ) = Q

  proof
    cQ
    cioo
    cq
    cq
    cxp
    #
    cima
    #
    ctg
    cfv
    #
    cioo
    crn
    #
    ctg
    cfv
    #
    tgqioo.1
    @1
    @3
    wss
    @3
    @2
    wss
    #
    @2
    @4
    wceq
    cioo
    @0
    imassrn
    cxr
    cxr
    cxp
    #
    @2
    cioo
    wf
    #
    @5
    @7
    cioo
    @6
    wfn
    #
    vx
    cv
    #
    vy
    cv
    #
    cioo
    co
    #
    @2
    wcel
    #
    vy
    cxr
    wral
    vx
    cxr
    wral
    @6
    cr
    cpw
    #
    cioo
    wf
    #
    @8
    ioof
    @6
    @13
    cioo
    ffn
    ax-mp
    @12
    vx
    vy
    cxr
    @9
    cxr
    wcel
    #
    @10
    cxr
    wcel
    #
    wa
    #
    vz
    cv
    #
    vw
    cv
    #
    wcel
    #
    @19
    @11
    wss
    #
    wa
    #
    vw
    @1
    wrex
    #
    vz
    @11
    wral
    #
    @12
    @17
    @23
    vz
    @11
    @17
    @18
    @11
    wcel
    #
    wa
    #
    @9
    vu
    cv
    #
    clt
    wbr
    #
    @27
    @18
    clt
    wbr
    #
    wa
    #
    vu
    cq
    wrex
    #
    @18
    vv
    cv
    #
    clt
    wbr
    #
    @32
    @10
    clt
    wbr
    #
    wa
    #
    vv
    cq
    wrex
    #
    @23
    @26
    @15
    @18
    cxr
    wcel
    #
    @9
    @18
    clt
    wbr
    #
    @31
    @15
    @16
    @25
    simpll
    #
    @26
    @37
    @38
    @18
    @10
    clt
    wbr
    #
    @17
    @25
    @37
    @38
    @40
    w3a
    @9
    @10
    @18
    elioo1
    biimpa
    #
    simp1d
    #
    @26
    @37
    @38
    @40
    @41
    simp2d
    vu
    @9
    @18
    qbtwnxr
    syl3anc
    @26
    @37
    @16
    @40
    @36
    @42
    @15
    @16
    @25
    simplr
    #
    @26
    @37
    @38
    @40
    @41
    simp3d
    vv
    @18
    @10
    qbtwnxr
    syl3anc
    @31
    @36
    wa
    @30
    @35
    wa
    #
    vv
    cq
    wrex
    vu
    cq
    wrex
    @26
    @23
    @30
    @35
    vu
    vv
    cq
    cq
    reeanv
    @26
    @44
    @23
    vu
    vv
    cq
    cq
    @26
    @27
    cq
    wcel
    #
    @32
    cq
    wcel
    #
    wa
    #
    @44
    @23
    @26
    @47
    @44
    w3a
    #
    @27
    @32
    cioo
    co
    #
    @1
    wcel
    @18
    @49
    wcel
    #
    @49
    @11
    wss
    #
    @23
    @48
    @49
    @27
    @32
    cop
    #
    cioo
    cfv
    #
    @1
    @27
    @32
    cioo
    df-ov
    @48
    @52
    @0
    wcel
    #
    @53
    @1
    wcel
    #
    @47
    @26
    @54
    @44
    @27
    @32
    cq
    cq
    opelxpi
    3ad2ant2
    cioo
    wfun
    #
    @0
    cioo
    cdm
    #
    wss
    @54
    @55
    wi
    @14
    @56
    ioof
    @6
    @13
    cioo
    ffun
    ax-mp
    @0
    @6
    @57
    cq
    cxr
    wss
    #
    @58
    @0
    @6
    wss
    cq
    cr
    cxr
    qssre
    ressxr
    sstri
    #
    @59
    cq
    cxr
    cq
    cxr
    xpss12
    mp2an
    @6
    @13
    cioo
    ioof
    fdmi
    sseqtr4i
    @0
    @52
    cioo
    funfvima2
    mp2an
    syl
    syl5eqel
    @48
    @50
    @37
    @29
    @33
    @26
    @47
    @37
    @44
    @42
    3ad2ant1
    @28
    @29
    @35
    @26
    @47
    simp3lr
    @33
    @34
    @30
    @26
    @47
    simp3rl
    @48
    @27
    cxr
    wcel
    #
    @32
    cxr
    wcel
    #
    @50
    @37
    @29
    @33
    w3a
    wb
    @48
    cq
    cxr
    @27
    @59
    @26
    @45
    @46
    @44
    simp2l
    sseldi
    #
    @48
    cq
    cxr
    @32
    @59
    @26
    @45
    @46
    @44
    simp2r
    sseldi
    #
    @27
    @32
    @18
    elioo1
    syl2anc
    mpbir3and
    @48
    @49
    @9
    @32
    cioo
    co
    #
    @11
    @48
    @15
    @9
    @27
    cle
    wbr
    #
    @49
    @64
    wss
    @26
    @47
    @15
    @44
    @39
    3ad2ant1
    #
    @48
    @28
    @65
    @28
    @29
    @35
    @26
    @47
    simp3ll
    @48
    @15
    @60
    @28
    @65
    wi
    @66
    @62
    @9
    @27
    xrltle
    syl2anc
    mpd
    @9
    @27
    @32
    iooss1
    syl2anc
    @48
    @16
    @32
    @10
    cle
    wbr
    #
    @64
    @11
    wss
    @26
    @47
    @16
    @44
    @43
    3ad2ant1
    #
    @48
    @34
    @67
    @33
    @34
    @30
    @26
    @47
    simp3rr
    @48
    @61
    @16
    @34
    @67
    wi
    @63
    @68
    @32
    @10
    xrltle
    syl2anc
    mpd
    @9
    @32
    @10
    iooss2
    syl2anc
    sstrd
    @22
    @50
    @51
    wa
    vw
    @49
    @1
    @19
    @49
    wceq
    @20
    @50
    @21
    @51
    @19
    @49
    @18
    eleq2
    @19
    @49
    @11
    sseq1
    anbi12d
    rspcev
    syl12anc
    3exp
    rexlimdvv
    syl5bir
    mp2and
    ralrimiva
    @1
    ctb
    wcel
    @12
    @24
    wb
    qtopbas
    vz
    vw
    @11
    @1
    ctb
    eltg2b
    ax-mp
    sylibr
    rgen2a
    vx
    vy
    cxr
    cxr
    @2
    cioo
    ffnov
    mpbir2an
    @6
    @2
    cioo
    frn
    ax-mp
    @1
    @3
    2basgen
    mp2an
    eqtr2i
end
