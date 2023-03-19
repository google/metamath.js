include "cc0.mm"
include "c1.mm"
include "cico.mm"
include "co.mm"
include "cpnf.mm"
include "clt.mm"
include "wiso.mm"
include "crest.mm"
include "chmeo.mm"
include "wcel.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "ccnv.mm"
include "caddc.mm"
include "cdiv.mm"
include "cmpt.mm"
include "wceq.mm"
include "icopnfcnv.mm"
include "simpli.mm"
include "wa.mm"
include "cmin.mm"
include "cmul.mm"
include "cr.mm"
include "cle.mm"
include "cxr.mm"
include "w3a.mm"
include "0re.mm"
include "1re.mm"
include "rexri.mm"
include "elico2.mm"
include "mp2an.mm"
include "simp1bi.mm"
include "ssriv.mm"
include "sseli.mm"
include "adantr.mm"
include "crp.mm"
include "simp3bi.mm"
include "difrp.mm"
include "sylancl.mm"
include "mpbid.mm"
include "rpregt0d.mm"
include "adantl.mm"
include "lt2mul2div.mm"
include "syl22anc.mm"
include "remulcld.mm"
include "ltsub1d.mm"
include "recnd.mm"
include "1cnd.mm"
include "subdid.mm"
include "mulid1d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "mulcomd.mm"
include "oveq12d.mm"
include "breq12d.mm"
include "bitr4d.mm"
include "id.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "breqan12d.mm"
include "3bitr4d.mm"
include "rgen2a.mm"
include "df-isom.mm"
include "mpbir2an.mm"
include "cxp.mm"
include "cin.mm"
include "cordt.mm"
include "cvv.mm"
include "ctsr.mm"
include "letsr.mm"
include "elexi.mm"
include "inex1.mm"
include "wss.mm"
include "icossxr.mm"
include "leiso.mm"
include "mpbi.mm"
include "isores1.mm"
include "isores2.mm"
include "cdm.mm"
include "cps.mm"
include "tsrps.mm"
include "ax-mp.mm"
include "ledm.mm"
include "psssdm.mm"
include "eqcomi.mm"
include "ordthmeo.mm"
include "mp3an.mm"
include "eqid.mm"
include "xrrest2.mm"
include "iccssico2.mm"
include "ordtrestixx.mm"
include "eqtri.mm"
include "rge0ssre.mm"
include "oveq12i.mm"
include "eleqtrri.mm"
include "pm3.2i.mm"

theorem icopnfhmeo
  let vx: setvar x
  let cF: class F
  let cJ: class J
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  let cG: class G
  assume icopnfhmeo.f: |- F = ( x e. ( 0 [,) 1 ) |-> ( x / ( 1 - x ) ) )
  assume icopnfhmeo.j: |- J = ( TopOpen ` CCfld )

  disjoint J x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G w
  disjoint G z
  disjoint v x
  disjoint J v
  disjoint w x
  disjoint J w
  disjoint x z
  disjoint J y
  disjoint J z
  assert |- ( F Isom < , < ( ( 0 [,) 1 ) , ( 0 [,) +oo ) ) /\ F e. ( ( J |`t ( 0 [,) 1 ) ) Homeo ( J |`t ( 0 [,) +oo ) ) ) )

  proof
    cc0
    c1
    cico
    co
    #
    cc0
    cpnf
    cico
    co
    #
    clt
    clt
    cF
    wiso
    #
    cF
    cJ
    @0
    crest
    co
    #
    cJ
    @1
    crest
    co
    #
    chmeo
    co
    #
    wcel
    @2
    @0
    @1
    cF
    wf1o
    #
    vz
    cv
    #
    vw
    cv
    #
    clt
    wbr
    #
    @7
    cF
    cfv
    #
    @8
    cF
    cfv
    #
    clt
    wbr
    #
    wb
    #
    vw
    @0
    wral
    vz
    @0
    wral
    @6
    cF
    ccnv
    vy
    @1
    vy
    cv
    #
    c1
    @14
    caddc
    co
    cdiv
    co
    cmpt
    wceq
    vx
    vy
    cF
    icopnfhmeo.f
    icopnfcnv
    simpli
    @13
    vz
    vw
    @0
    @7
    @0
    wcel
    #
    @8
    @0
    wcel
    #
    wa
    #
    @7
    c1
    @8
    cmin
    co
    #
    cmul
    co
    #
    @8
    c1
    @7
    cmin
    co
    #
    cmul
    co
    #
    clt
    wbr
    #
    @7
    @20
    cdiv
    co
    #
    @8
    @18
    cdiv
    co
    #
    clt
    wbr
    #
    @9
    @12
    @17
    @7
    cr
    wcel
    #
    @18
    cr
    wcel
    cc0
    @18
    clt
    wbr
    wa
    #
    @8
    cr
    wcel
    #
    @20
    cr
    wcel
    cc0
    @20
    clt
    wbr
    wa
    @22
    @25
    wb
    @15
    @26
    @16
    @0
    cr
    @7
    vx
    @0
    cr
    vx
    cv
    #
    @0
    wcel
    #
    @29
    cr
    wcel
    #
    cc0
    @29
    cle
    wbr
    #
    @29
    c1
    clt
    wbr
    #
    cc0
    cr
    wcel
    #
    c1
    cxr
    wcel
    #
    @30
    @31
    @32
    @33
    w3a
    wb
    0re
    c1
    1re
    rexri
    #
    cc0
    c1
    @29
    elico2
    mp2an
    simp1bi
    ssriv
    #
    sseli
    #
    adantr
    #
    @16
    @27
    @15
    @16
    @18
    @16
    @8
    c1
    clt
    wbr
    #
    @18
    crp
    wcel
    #
    @16
    @28
    cc0
    @8
    cle
    wbr
    #
    @40
    @34
    @35
    @16
    @28
    @42
    @40
    w3a
    wb
    0re
    @36
    cc0
    c1
    @8
    elico2
    mp2an
    simp3bi
    @16
    @28
    c1
    cr
    wcel
    #
    @40
    @41
    wb
    @0
    cr
    @8
    @37
    sseli
    #
    1re
    @8
    c1
    difrp
    sylancl
    mpbid
    rpregt0d
    adantl
    @16
    @28
    @15
    @44
    adantl
    #
    @17
    @20
    @15
    @20
    crp
    wcel
    #
    @16
    @15
    @7
    c1
    clt
    wbr
    #
    @46
    @15
    @26
    cc0
    @7
    cle
    wbr
    #
    @47
    @34
    @35
    @15
    @26
    @48
    @47
    w3a
    wb
    0re
    @36
    cc0
    c1
    @7
    elico2
    mp2an
    simp3bi
    @15
    @26
    @43
    @47
    @46
    wb
    @38
    1re
    @7
    c1
    difrp
    sylancl
    mpbid
    adantr
    rpregt0d
    @7
    @18
    @8
    @20
    lt2mul2div
    syl22anc
    @17
    @9
    @7
    @7
    @8
    cmul
    co
    #
    cmin
    co
    #
    @8
    @49
    cmin
    co
    #
    clt
    wbr
    @22
    @17
    @7
    @8
    @49
    @39
    @45
    @17
    @7
    @8
    @39
    @45
    remulcld
    ltsub1d
    @17
    @19
    @50
    @21
    @51
    clt
    @17
    @19
    @7
    c1
    cmul
    co
    #
    @49
    cmin
    co
    @50
    @17
    @7
    c1
    @8
    @17
    @7
    @39
    recnd
    #
    @17
    1cnd
    #
    @17
    @8
    @45
    recnd
    #
    subdid
    @17
    @52
    @7
    @49
    cmin
    @17
    @7
    @53
    mulid1d
    oveq1d
    eqtrd
    @17
    @21
    @8
    c1
    cmul
    co
    #
    @8
    @7
    cmul
    co
    #
    cmin
    co
    @51
    @17
    @8
    c1
    @7
    @55
    @54
    @53
    subdid
    @17
    @56
    @8
    @57
    @49
    cmin
    @17
    @8
    @55
    mulid1d
    @17
    @8
    @7
    @55
    @53
    mulcomd
    oveq12d
    eqtrd
    breq12d
    bitr4d
    @15
    @16
    @10
    @23
    @11
    @24
    clt
    vx
    @7
    @29
    c1
    @29
    cmin
    co
    #
    cdiv
    co
    #
    @23
    @0
    cF
    @29
    @7
    wceq
    #
    @29
    @7
    @58
    @20
    cdiv
    @60
    id
    @29
    @7
    c1
    cmin
    oveq2
    oveq12d
    icopnfhmeo.f
    @7
    @20
    cdiv
    ovex
    fvmpt
    vx
    @8
    @59
    @24
    @0
    cF
    @29
    @8
    wceq
    #
    @29
    @8
    @58
    @18
    cdiv
    @61
    id
    @29
    @8
    c1
    cmin
    oveq2
    oveq12d
    icopnfhmeo.f
    @8
    @18
    cdiv
    ovex
    fvmpt
    breqan12d
    3bitr4d
    rgen2a
    vz
    vw
    @0
    @1
    clt
    clt
    cF
    df-isom
    mpbir2an
    #
    cF
    cle
    @0
    @0
    cxp
    #
    cin
    #
    cordt
    cfv
    #
    cle
    @1
    @1
    cxp
    #
    cin
    #
    cordt
    cfv
    #
    chmeo
    co
    #
    @5
    @64
    cvv
    wcel
    @67
    cvv
    wcel
    @0
    @1
    @64
    @67
    cF
    wiso
    #
    cF
    @69
    wcel
    cle
    @63
    cle
    ctsr
    letsr
    elexi
    #
    inex1
    cle
    @66
    @71
    inex1
    @0
    @1
    @64
    cle
    cF
    wiso
    #
    @70
    @0
    @1
    cle
    cle
    cF
    wiso
    #
    @72
    @2
    @73
    @62
    @0
    cxr
    wss
    #
    @1
    cxr
    wss
    #
    @2
    @73
    wb
    cc0
    c1
    icossxr
    #
    cc0
    cpnf
    icossxr
    #
    @0
    @1
    cF
    leiso
    mp2an
    mpbi
    @0
    @1
    cle
    cle
    cF
    isores1
    mpbi
    @0
    @1
    @64
    cle
    cF
    isores2
    mpbi
    @64
    @67
    cF
    cvv
    cvv
    @0
    @1
    @64
    cdm
    #
    @0
    cle
    cps
    wcel
    #
    @74
    @78
    @0
    wceq
    cle
    ctsr
    wcel
    @79
    letsr
    cle
    tsrps
    ax-mp
    #
    @76
    @0
    cle
    cxr
    ledm
    psssdm
    mp2an
    eqcomi
    @67
    cdm
    #
    @1
    @79
    @75
    @81
    @1
    wceq
    @80
    @77
    @1
    cle
    cxr
    ledm
    psssdm
    mp2an
    eqcomi
    ordthmeo
    mp3an
    @3
    @65
    @4
    @68
    chmeo
    @3
    cle
    cordt
    cfv
    #
    @0
    crest
    co
    #
    @65
    @0
    cr
    wss
    @3
    @83
    wceq
    @37
    @0
    cJ
    @82
    icopnfhmeo.j
    @82
    eqid
    #
    xrrest2
    ax-mp
    vx
    vy
    @0
    @76
    cc0
    c1
    @29
    @14
    iccssico2
    ordtrestixx
    eqtri
    @4
    @82
    @1
    crest
    co
    #
    @68
    @1
    cr
    wss
    @4
    @85
    wceq
    rge0ssre
    @1
    cJ
    @82
    icopnfhmeo.j
    @84
    xrrest2
    ax-mp
    vx
    vy
    @1
    @77
    cc0
    cpnf
    @29
    @14
    iccssico2
    ordtrestixx
    eqtri
    oveq12i
    eleqtrri
    pm3.2i
end
