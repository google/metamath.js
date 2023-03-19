include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "clt.mm"
include "wor.mm"
include "cpnf.mm"
include "ccnv.mm"
include "wpo.mm"
include "wfo.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "wiso.mm"
include "cxr.mm"
include "wss.mm"
include "iccssxr.mm"
include "xrltso.mm"
include "soss.mm"
include "mp2.mm"
include "cnvso.mm"
include "mpbi.mm"
include "sopo.mm"
include "ax-mp.mm"
include "poss.mm"
include "wf1o.mm"
include "wceq.mm"
include "cneg.mm"
include "ce.mm"
include "cif.mm"
include "cmpt.mm"
include "xrge0iifcnv.mm"
include "simpli.mm"
include "f1ofo.mm"
include "wcel.mm"
include "csn.mm"
include "cioc.mm"
include "wo.mm"
include "cun.mm"
include "cle.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "0le1.mm"
include "snunioc.mm"
include "mp3an.mm"
include "eleq2i.mm"
include "elun.mm"
include "bitr3i.mm"
include "velsn.mm"
include "wa.mm"
include "cr.mm"
include "elunitrn.mm"
include "adantr.mm"
include "simpr.mm"
include "0re.mm"
include "elicc2i.mm"
include "simp3bi.mm"
include "w3a.mm"
include "wb.mm"
include "elioc2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "clog.mm"
include "crp.mm"
include "cioo.mm"
include "pnfxr.mm"
include "0le0.mm"
include "ltpnf.mm"
include "iocssioo.mm"
include "mp4an.mm"
include "ioorp.mm"
include "sseqtri.mm"
include "sseli.mm"
include "relogcl.mm"
include "renegcld.mm"
include "syl.mm"
include "brcnvg.mm"
include "sylancr.mm"
include "mpbird.mm"
include "xrge0iifcv.mm"
include "breqtrrd.mm"
include "ex.mm"
include "breq1.mm"
include "fveq2.mm"
include "0elunit.mm"
include "iftrue.mm"
include "pnfex.mm"
include "fvmpt.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "syl5ibr.mm"
include "sylbi.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "a1i.mm"
include "rpred.mm"
include "ad2antrr.mm"
include "simp2bi.mm"
include "lttrd.mm"
include "jca.mm"
include "relogcld.mm"
include "adantl.mm"
include "ltnegd.mm"
include "logltb.mm"
include "syl2an.mm"
include "negex.mm"
include "brcnv.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "breqan12d.mm"
include "sylibrd.mm"
include "sylc.mm"
include "exp31.mm"
include "jaoi.mm"
include "imp.mm"
include "rgen2a.mm"
include "soisoi.mm"

theorem xrge0iifiso
  let vx: setvar x
  let cF: class F
  let vy: setvar y
  let cX: class X
  let vw: setvar w
  let vz: setvar z
  assume xrge0iifhmeo.1: |- F = ( x e. ( 0 [,] 1 ) |-> if ( x = 0 , +oo , -u ( log ` x ) ) )

  disjoint F x
  disjoint x y
  disjoint X x
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  assert |- F Isom < , `' < ( ( 0 [,] 1 ) , ( 0 [,] +oo ) )

  proof
    cc0
    c1
    cicc
    co
    #
    clt
    wor
    #
    cc0
    cpnf
    cicc
    co
    #
    clt
    ccnv
    #
    wpo
    #
    @0
    @2
    cF
    wfo
    #
    vw
    cv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @6
    cF
    cfv
    #
    @7
    cF
    cfv
    #
    @3
    wbr
    #
    wi
    #
    vz
    @0
    wral
    vw
    @0
    wral
    @0
    @2
    clt
    @3
    cF
    wiso
    @0
    cxr
    wss
    cxr
    clt
    wor
    #
    @1
    cc0
    c1
    iccssxr
    xrltso
    @0
    cxr
    clt
    soss
    mp2
    @2
    cxr
    wss
    cxr
    @3
    wpo
    #
    @4
    cc0
    cpnf
    iccssxr
    cxr
    @3
    wor
    #
    @14
    @13
    @15
    xrltso
    cxr
    clt
    cnvso
    mpbi
    cxr
    @3
    sopo
    ax-mp
    @2
    cxr
    @3
    poss
    mp2
    @0
    @2
    cF
    wf1o
    #
    @5
    @16
    cF
    ccnv
    vz
    @2
    @7
    cpnf
    wceq
    cc0
    @7
    cneg
    ce
    cfv
    cif
    cmpt
    wceq
    vx
    vz
    cF
    xrge0iifhmeo.1
    xrge0iifcnv
    simpli
    @0
    @2
    cF
    f1ofo
    ax-mp
    @12
    vw
    vz
    @0
    @6
    @0
    wcel
    #
    @7
    @0
    wcel
    #
    @12
    @17
    @6
    cc0
    csn
    #
    wcel
    #
    @6
    cc0
    c1
    cioc
    co
    #
    wcel
    #
    wo
    #
    @18
    @12
    wi
    #
    @17
    @6
    @19
    @21
    cun
    #
    wcel
    @23
    @25
    @0
    @6
    cc0
    cxr
    wcel
    #
    c1
    cxr
    wcel
    cc0
    c1
    cle
    wbr
    @25
    @0
    wceq
    0xr
    c1
    1re
    rexri
    0le1
    cc0
    c1
    snunioc
    mp3an
    eleq2i
    @6
    @19
    @21
    elun
    bitr3i
    @20
    @24
    @22
    @20
    @6
    cc0
    wceq
    #
    @24
    vw
    cc0
    velsn
    @18
    @12
    @27
    cc0
    @7
    clt
    wbr
    #
    cpnf
    @10
    @3
    wbr
    #
    wi
    @18
    @28
    @29
    @18
    @28
    wa
    #
    @7
    @21
    wcel
    #
    @29
    @30
    @7
    cr
    wcel
    #
    @28
    @7
    c1
    cle
    wbr
    #
    @31
    @18
    @32
    @28
    @7
    elunitrn
    #
    adantr
    @18
    @28
    simpr
    @18
    @33
    @28
    @18
    @32
    cc0
    @7
    cle
    wbr
    @33
    cc0
    c1
    @7
    0re
    1re
    elicc2i
    simp3bi
    #
    adantr
    @26
    c1
    cr
    wcel
    #
    @31
    @32
    @28
    @33
    w3a
    wb
    0xr
    1re
    cc0
    c1
    @7
    elioc2
    mp2an
    #
    syl3anbrc
    @31
    cpnf
    @7
    clog
    cfv
    #
    cneg
    #
    @10
    @3
    @31
    @7
    crp
    wcel
    #
    cpnf
    @39
    @3
    wbr
    #
    @21
    crp
    @7
    @21
    cc0
    cpnf
    cioo
    co
    #
    crp
    @26
    cpnf
    cxr
    wcel
    #
    cc0
    cc0
    cle
    wbr
    c1
    cpnf
    clt
    wbr
    #
    @21
    @42
    wss
    0xr
    pnfxr
    0le0
    @36
    @44
    1re
    c1
    ltpnf
    ax-mp
    cc0
    cpnf
    cc0
    c1
    iocssioo
    mp4an
    ioorp
    sseqtri
    #
    sseli
    #
    @40
    @41
    @39
    cpnf
    clt
    wbr
    #
    @40
    @39
    cr
    wcel
    #
    @47
    @40
    @38
    @7
    relogcl
    renegcld
    #
    @39
    ltpnf
    syl
    @40
    @43
    @48
    @41
    @47
    wb
    pnfxr
    @49
    cpnf
    @39
    cxr
    cr
    clt
    brcnvg
    sylancr
    mpbird
    syl
    vx
    cF
    @7
    xrge0iifhmeo.1
    xrge0iifcv
    #
    breqtrrd
    syl
    ex
    @27
    @8
    @28
    @11
    @29
    @6
    cc0
    @7
    clt
    breq1
    @27
    @9
    cpnf
    @10
    @3
    @27
    @9
    cc0
    cF
    cfv
    #
    cpnf
    @6
    cc0
    cF
    fveq2
    cc0
    @0
    wcel
    @51
    cpnf
    wceq
    0elunit
    vx
    cc0
    vx
    cv
    #
    cc0
    wceq
    #
    cpnf
    @52
    clog
    cfv
    cneg
    #
    cif
    cpnf
    @0
    cF
    @53
    cpnf
    @54
    iftrue
    xrge0iifhmeo.1
    pnfex
    fvmpt
    ax-mp
    syl6eq
    breq1d
    imbi12d
    syl5ibr
    sylbi
    @22
    @18
    @8
    @11
    @22
    @18
    wa
    #
    @8
    wa
    #
    @22
    @31
    wa
    #
    @8
    @11
    @56
    @22
    @31
    @22
    @18
    @8
    simpll
    @56
    @32
    @28
    @33
    @31
    @18
    @32
    @22
    @8
    @34
    ad2antlr
    #
    @56
    cc0
    @6
    @7
    cc0
    cr
    wcel
    @56
    0re
    a1i
    @22
    @6
    cr
    wcel
    #
    @18
    @8
    @22
    @6
    @21
    crp
    @6
    @45
    sseli
    #
    rpred
    ad2antrr
    @58
    @22
    cc0
    @6
    clt
    wbr
    #
    @18
    @8
    @22
    @59
    @61
    @6
    c1
    cle
    wbr
    #
    @26
    @36
    @22
    @59
    @61
    @62
    w3a
    wb
    0xr
    1re
    cc0
    c1
    @6
    elioc2
    mp2an
    simp2bi
    ad2antrr
    @55
    @8
    simpr
    #
    lttrd
    @18
    @33
    @22
    @8
    @35
    ad2antlr
    @37
    syl3anbrc
    jca
    @63
    @57
    @8
    @6
    clog
    cfv
    #
    cneg
    #
    @39
    @3
    wbr
    #
    @11
    @57
    @8
    @66
    @57
    @64
    @38
    clt
    wbr
    #
    @39
    @65
    clt
    wbr
    #
    @8
    @66
    @57
    @64
    @38
    @57
    @6
    @22
    @6
    crp
    wcel
    #
    @31
    @60
    adantr
    relogcld
    @57
    @7
    @31
    @40
    @22
    @46
    adantl
    relogcld
    ltnegd
    @22
    @69
    @40
    @8
    @67
    wb
    @31
    @60
    @46
    @6
    @7
    logltb
    syl2an
    @66
    @68
    wb
    @57
    @65
    @39
    clt
    @64
    negex
    @38
    negex
    brcnv
    a1i
    3bitr4d
    biimpd
    @22
    @31
    @9
    @65
    @10
    @39
    @3
    vx
    cF
    @6
    xrge0iifhmeo.1
    xrge0iifcv
    @50
    breqan12d
    sylibrd
    sylc
    exp31
    jaoi
    sylbi
    imp
    rgen2a
    vw
    vz
    @0
    @2
    clt
    @3
    cF
    soisoi
    mp4an
end
