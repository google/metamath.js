include "clvec.mm"
include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "lbsss.mm"
include "adantl.mm"
include "lbssp.mm"
include "clmod.mm"
include "csca.mm"
include "cur.mm"
include "c0g.mm"
include "wne.mm"
include "lveclmod.mm"
include "cdr.mm"
include "eqid.mm"
include "lvecdrng.mm"
include "drngunz.mm"
include "syl.mm"
include "jca.mm"
include "lbsind2.mm"
include "syl3an1.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "cvsca.mm"
include "co.mm"
include "cbs.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simprl.mm"
include "simplr3.mm"
include "id.mm"
include "sneq.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "rspcv.mm"
include "sylc.mm"
include "simpll.mm"
include "simprr.mm"
include "eldifsn.mm"
include "sylib.mm"
include "adantr.mm"
include "sseldd.mm"
include "lspsnvs.mm"
include "syl3anc.mm"
include "sseq1d.mm"
include "clss.mm"
include "ssdifssd.mm"
include "lspcl.mm"
include "syl2anc.mm"
include "simpld.mm"
include "lmodvscl.mm"
include "lspsnel5.mm"
include "3bitr4d.mm"
include "mtbird.mm"
include "ralrimivva.mm"
include "wb.mm"
include "islbs.mm"
include "mpbir3and.mm"
include "impbida.mm"

theorem islbs2
  let vx: setvar x
  let cB: class B
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  assume islbs2.v: |- V = ( Base ` W )
  assume islbs2.j: |- J = ( LBasis ` W )
  assume islbs2.n: |- N = ( LSpan ` W )

  disjoint B x
  disjoint N x
  disjoint V x
  disjoint W x
  disjoint J x
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint N s
  disjoint N y
  disjoint N z
  disjoint V s
  disjoint V y
  disjoint V z
  disjoint W s
  disjoint W y
  disjoint W z
  disjoint J s
  assert |- ( W e. LVec -> ( B e. J <-> ( B C_ V /\ ( N ` B ) = V /\ A. x e. B -. x e. ( N ` ( B \ { x } ) ) ) ) )

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
    cV
    wceq
    #
    vx
    cv
    #
    cB
    @4
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
    w3a
    #
    @0
    @1
    wa
    #
    @2
    @3
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
    adantl
    @1
    @3
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
    vx
    cB
    @0
    @1
    @4
    cB
    wcel
    #
    @9
    @0
    cW
    clmod
    wcel
    #
    cW
    csca
    cfv
    #
    cur
    cfv
    #
    @15
    c0g
    cfv
    #
    wne
    #
    wa
    @1
    @13
    @9
    @0
    @14
    @18
    cW
    lveclmod
    #
    @0
    @15
    cdr
    wcel
    @18
    @15
    cW
    @15
    eqid
    #
    lvecdrng
    @15
    @16
    @17
    @17
    eqid
    #
    @16
    eqid
    #
    drngunz
    syl
    jca
    cB
    @16
    @4
    @15
    cJ
    cN
    cW
    @17
    islbs2.j
    islbs2.n
    @20
    @22
    @21
    lbsind2
    syl3an1
    3expa
    ralrimiva
    3jca
    @0
    @11
    wa
    #
    @1
    @2
    @3
    vz
    cv
    #
    vy
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    cB
    @25
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
    vz
    @15
    cbs
    cfv
    #
    @17
    csn
    cdif
    #
    wral
    vy
    cB
    wral
    #
    @0
    @2
    @3
    @10
    simpr1
    #
    @0
    @2
    @3
    @10
    simpr2
    @23
    @32
    vy
    vz
    cB
    @34
    @23
    @25
    cB
    wcel
    #
    @24
    @34
    wcel
    #
    wa
    #
    wa
    #
    @31
    @25
    @30
    wcel
    #
    @40
    @37
    @10
    @41
    wn
    #
    @23
    @37
    @38
    simprl
    #
    @2
    @3
    @10
    @0
    @39
    simplr3
    @9
    @42
    vx
    @25
    cB
    @4
    @25
    wceq
    #
    @8
    @41
    @44
    @4
    @25
    @7
    @30
    @44
    id
    @44
    @6
    @29
    cN
    @44
    @5
    @28
    cB
    @4
    @25
    sneq
    difeq2d
    fveq2d
    eleq12d
    notbid
    rspcv
    sylc
    @40
    @27
    csn
    cN
    cfv
    #
    @30
    wss
    @28
    cN
    cfv
    #
    @30
    wss
    @31
    @41
    @40
    @45
    @46
    @30
    @40
    @0
    @24
    @33
    wcel
    #
    @24
    @17
    wne
    #
    wa
    #
    @25
    cV
    wcel
    #
    @45
    @46
    wceq
    @0
    @11
    @39
    simpll
    @40
    @38
    @49
    @23
    @37
    @38
    simprr
    @24
    @33
    @17
    eldifsn
    sylib
    #
    @40
    cB
    cV
    @25
    @23
    @2
    @39
    @36
    adantr
    #
    @43
    sseldd
    #
    @24
    @26
    @15
    @33
    cN
    cV
    cW
    @25
    @17
    islbs2.v
    @20
    @26
    eqid
    #
    @33
    eqid
    #
    @21
    islbs2.n
    lspsnvs
    syl3anc
    sseq1d
    @40
    cW
    clss
    cfv
    #
    @30
    cN
    cV
    cW
    @27
    islbs2.v
    @56
    eqid
    #
    islbs2.n
    @23
    @14
    @39
    @0
    @14
    @11
    @19
    adantr
    adantr
    #
    @40
    @14
    @29
    cV
    wss
    @30
    @56
    wcel
    @58
    @40
    cB
    cV
    @28
    @52
    ssdifssd
    @56
    @29
    cN
    cV
    cW
    islbs2.v
    @57
    islbs2.n
    lspcl
    syl2anc
    #
    @40
    @14
    @47
    @50
    @27
    cV
    wcel
    @58
    @40
    @47
    @48
    @51
    simpld
    @53
    @24
    @26
    @15
    @33
    cV
    cW
    @25
    islbs2.v
    @20
    @54
    @55
    lmodvscl
    syl3anc
    lspsnel5
    @40
    @56
    @30
    cN
    cV
    cW
    @25
    islbs2.v
    @57
    islbs2.n
    @58
    @59
    @53
    lspsnel5
    3bitr4d
    mtbird
    ralrimivva
    @0
    @1
    @2
    @3
    @35
    w3a
    wb
    @11
    vy
    vz
    cB
    @26
    @15
    cJ
    @33
    cN
    cV
    cW
    clvec
    @17
    islbs2.v
    @20
    @54
    @55
    islbs2.j
    islbs2.n
    @21
    islbs
    adantr
    mpbir3and
    impbida
end
