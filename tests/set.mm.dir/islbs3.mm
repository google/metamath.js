include "clvec.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wpss.mm"
include "wi.mm"
include "wal.mm"
include "w3a.mm"
include "wa.mm"
include "lbsss.mm"
include "adantl.mm"
include "lbssp.mm"
include "wne.mm"
include "clmod.mm"
include "lveclmod.mm"
include "3ad2ant1.mm"
include "pssss.mm"
include "sylan9ssr.mm"
include "3adant1.mm"
include "lspssv.mm"
include "syl2anc.mm"
include "csca.mm"
include "cur.mm"
include "c0g.mm"
include "cdr.mm"
include "eqid.mm"
include "lvecdrng.mm"
include "drngunz.mm"
include "syl.mm"
include "jca.mm"
include "lbspss.mm"
include "syl3an1.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "3expia.mm"
include "alrimiv.mm"
include "3jca.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wral.mm"
include "simpr1.mm"
include "simpr2.mm"
include "cvv.mm"
include "simplr1.mm"
include "ssdifssd.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssexg.mm"
include "sylancl.mm"
include "simplr3.mm"
include "difssd.mm"
include "simpr.mm"
include "neldifsn.mm"
include "nelne1.mm"
include "necomd.mm"
include "psseq1.mm"
include "fveq2.mm"
include "psseq1d.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl3c.mm"
include "dfpss3.mm"
include "simprbi.mm"
include "simplr2.mm"
include "clss.mm"
include "ad2antrr.mm"
include "adantrr.mm"
include "lspcl.mm"
include "cun.mm"
include "ssun1.mm"
include "undif1.mm"
include "sseqtr4i.mm"
include "lspssid.mm"
include "simprr.mm"
include "snssd.mm"
include "unssd.mm"
include "syl5ss.mm"
include "lspssp.mm"
include "syl3anc.mm"
include "eqsstr3d.mm"
include "expr.mm"
include "mtod.mm"
include "ralrimiva.mm"
include "wb.mm"
include "islbs2.mm"
include "adantr.mm"
include "mpbir3and.mm"
include "impbida.mm"

theorem islbs3
  let cB: class B
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume islbs2.v: |- V = ( Base ` W )
  assume islbs2.j: |- J = ( LBasis ` W )
  assume islbs2.n: |- N = ( LSpan ` W )

  disjoint B s
  disjoint N s
  disjoint V s
  disjoint W s
  disjoint J s
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint J x
  assert |- ( W e. LVec -> ( B e. J <-> ( B C_ V /\ ( N ` B ) = V /\ A. s ( s C. B -> ( N ` s ) C. V ) ) ) )

  proof
    cW
    clvec
    wcel
    #
    cB
    cJ
    wcel
    #
    cB
    cV
    wss
    #
    cB
    cN
    cfv
    #
    cV
    wceq
    #
    vs
    cv
    #
    cB
    wpss
    #
    @5
    cN
    cfv
    #
    cV
    wpss
    #
    wi
    #
    vs
    wal
    #
    w3a
    #
    @0
    @1
    wa
    #
    @2
    @4
    @10
    @1
    @2
    @0
    cB
    cJ
    cV
    cW
    islbs2.v
    islbs2.j
    lbsss
    #
    adantl
    @1
    @4
    @0
    cB
    cJ
    cN
    cV
    cW
    islbs2.v
    islbs2.j
    islbs2.n
    lbssp
    adantl
    @12
    @9
    vs
    @0
    @1
    @6
    @8
    @0
    @1
    @6
    w3a
    #
    @7
    cV
    wss
    #
    @7
    cV
    wne
    #
    @8
    @14
    cW
    clmod
    wcel
    #
    @5
    cV
    wss
    #
    @15
    @0
    @1
    @17
    @6
    cW
    lveclmod
    #
    3ad2ant1
    @1
    @6
    @18
    @0
    @6
    @1
    @5
    cB
    cV
    @5
    cB
    pssss
    @13
    sylan9ssr
    3adant1
    @5
    cN
    cV
    cW
    islbs2.v
    islbs2.n
    lspssv
    syl2anc
    @0
    @17
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @20
    c0g
    cfv
    #
    wne
    #
    wa
    @1
    @6
    @16
    @0
    @17
    @23
    @19
    @0
    @20
    cdr
    wcel
    @23
    @20
    cW
    @20
    eqid
    #
    lvecdrng
    @20
    @21
    @22
    @22
    eqid
    #
    @21
    eqid
    #
    drngunz
    syl
    jca
    cB
    @5
    @21
    @20
    cJ
    cN
    cV
    cW
    @22
    islbs2.j
    islbs2.n
    @24
    @26
    @25
    islbs2.v
    lbspss
    syl3an1
    @7
    cV
    df-pss
    sylanbrc
    3expia
    alrimiv
    3jca
    @0
    @11
    wa
    #
    @1
    @2
    @4
    vx
    cv
    #
    cB
    @28
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    cB
    wral
    #
    @0
    @2
    @4
    @10
    simpr1
    @0
    @2
    @4
    @10
    simpr2
    @27
    @33
    vx
    cB
    @27
    @28
    cB
    wcel
    #
    wa
    #
    @32
    cV
    @31
    wss
    #
    @36
    @31
    cV
    wpss
    #
    @37
    wn
    #
    @36
    @30
    cvv
    wcel
    #
    @10
    @30
    cB
    wpss
    #
    @38
    @36
    @30
    cV
    wss
    #
    cV
    cvv
    wcel
    @40
    @36
    cB
    cV
    @29
    @2
    @4
    @10
    @0
    @35
    simplr1
    ssdifssd
    #
    cV
    cW
    cbs
    cfv
    cvv
    islbs2.v
    cW
    cbs
    fvex
    eqeltri
    @30
    cV
    cvv
    ssexg
    sylancl
    @2
    @4
    @10
    @0
    @35
    simplr3
    @36
    @30
    cB
    wss
    @30
    cB
    wne
    @41
    @36
    cB
    @29
    difssd
    @36
    cB
    @30
    @36
    @35
    @28
    @30
    wcel
    wn
    cB
    @30
    wne
    @27
    @35
    simpr
    @28
    cB
    neldifsn
    @28
    cB
    @30
    nelne1
    sylancl
    necomd
    @30
    cB
    df-pss
    sylanbrc
    @9
    @41
    @38
    wi
    vs
    @30
    cvv
    @5
    @30
    wceq
    #
    @6
    @41
    @8
    @38
    @5
    @30
    cB
    psseq1
    @44
    @7
    @31
    cV
    @5
    @30
    cN
    fveq2
    psseq1d
    imbi12d
    spcgv
    syl3c
    @38
    @31
    cV
    wss
    @39
    @31
    cV
    dfpss3
    simprbi
    syl
    @27
    @35
    @32
    @37
    @27
    @35
    @32
    wa
    #
    wa
    #
    cV
    @3
    @31
    @2
    @4
    @10
    @0
    @45
    simplr2
    @46
    @17
    @31
    cW
    clss
    cfv
    #
    wcel
    #
    cB
    @31
    wss
    @3
    @31
    wss
    @0
    @17
    @11
    @45
    @19
    ad2antrr
    #
    @46
    @17
    @42
    @48
    @49
    @27
    @35
    @42
    @32
    @43
    adantrr
    #
    @47
    @30
    cN
    cV
    cW
    islbs2.v
    @47
    eqid
    #
    islbs2.n
    lspcl
    syl2anc
    @46
    cB
    @30
    @29
    cun
    #
    @31
    cB
    cB
    @29
    cun
    @52
    cB
    @29
    ssun1
    cB
    @29
    undif1
    sseqtr4i
    @46
    @30
    @29
    @31
    @46
    @17
    @42
    @30
    @31
    wss
    @49
    @50
    @30
    cN
    cV
    cW
    islbs2.v
    islbs2.n
    lspssid
    syl2anc
    @46
    @28
    @31
    @27
    @35
    @32
    simprr
    snssd
    unssd
    syl5ss
    @47
    cB
    @31
    cN
    cW
    @51
    islbs2.n
    lspssp
    syl3anc
    eqsstr3d
    expr
    mtod
    ralrimiva
    @0
    @1
    @2
    @4
    @34
    w3a
    wb
    @11
    vx
    cB
    cJ
    cN
    cV
    cW
    islbs2.v
    islbs2.j
    islbs2.n
    islbs2
    adantr
    mpbir3and
    impbida
end
