include "cobs.mm"
include "cfv.mm"
include "wcel.mm"
include "cocv.mm"
include "wceq.mm"
include "cbs.mm"
include "cphl.mm"
include "wss.mm"
include "obsrcl.mm"
include "eqid.mm"
include "obsss.mm"
include "ocvlsp.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "obs2ocv.mm"
include "eqtrd.mm"
include "eqeq2d.mm"
include "wb.mm"
include "iscss.mm"
include "syl.mm"
include "clvec.mm"
include "cv.mm"
include "wpss.mm"
include "wi.mm"
include "wal.mm"
include "phllvec.mm"
include "wa.mm"
include "wn.mm"
include "wex.mm"
include "pssnel.mm"
include "adantl.mm"
include "c0g.mm"
include "csn.mm"
include "wne.mm"
include "simpll.mm"
include "pssss.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "obselocv.mm"
include "syl3anc.mm"
include "obsne0.mm"
include "nelsn.mm"
include "nelne1.mm"
include "expcom.mm"
include "sylbird.mm"
include "npss.mm"
include "clmod.mm"
include "phllmod.mm"
include "ad2antrr.mm"
include "sstrd.mm"
include "lspssv.mm"
include "fveq2.mm"
include "ocv1.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "embantd.mm"
include "syl5bi.mm"
include "necon1ad.mm"
include "syld.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "mpd.mm"
include "ex.mm"
include "alrimiv.mm"
include "w3a.mm"
include "islbs3.mm"
include "3anan32.mm"
include "syl6bb.mm"
include "baibd.mm"
include "syl12anc.mm"
include "3bitr4rd.mm"

theorem obslbs
  let cB: class B
  let cC: class C
  let cJ: class J
  let cN: class N
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume obslbs.j: |- J = ( LBasis ` W )
  assume obslbs.n: |- N = ( LSpan ` W )
  assume obslbs.c: |- C = ( CSubSp ` W )


  assert |- ( B e. ( OBasis ` W ) -> ( B e. J <-> ( N ` B ) e. C ) )

  proof
    cB
    cW
    cobs
    cfv
    wcel
    #
    cB
    cN
    cfv
    #
    @1
    cW
    cocv
    cfv
    #
    cfv
    #
    @2
    cfv
    #
    wceq
    #
    @1
    cW
    cbs
    cfv
    #
    wceq
    #
    @1
    cC
    wcel
    #
    cB
    cJ
    wcel
    #
    @0
    @4
    @6
    @1
    @0
    @4
    cB
    @2
    cfv
    #
    @2
    cfv
    @6
    @0
    @3
    @10
    @2
    @0
    cW
    cphl
    wcel
    #
    cB
    @6
    wss
    #
    @3
    @10
    wceq
    cB
    cW
    obsrcl
    #
    cB
    @6
    cW
    @6
    eqid
    #
    obsss
    #
    cB
    cN
    @2
    @6
    cW
    @14
    @2
    eqid
    #
    obslbs.n
    ocvlsp
    syl2anc
    fveq2d
    cB
    @2
    @6
    cW
    @16
    @14
    obs2ocv
    eqtrd
    eqeq2d
    @0
    @11
    @8
    @5
    wb
    @13
    cC
    @1
    @2
    cW
    cphl
    @16
    obslbs.c
    iscss
    syl
    @0
    cW
    clvec
    wcel
    #
    @12
    vx
    cv
    #
    cB
    wpss
    #
    @18
    cN
    cfv
    #
    @6
    wpss
    #
    wi
    #
    vx
    wal
    #
    @9
    @7
    wb
    @0
    @11
    @17
    @13
    cW
    phllvec
    syl
    @15
    @0
    @22
    vx
    @0
    @19
    @21
    @0
    @19
    wa
    #
    vy
    cv
    #
    cB
    wcel
    #
    @25
    @18
    wcel
    wn
    #
    wa
    #
    vy
    wex
    #
    @21
    @19
    @29
    @0
    vy
    @18
    cB
    pssnel
    adantl
    @24
    @28
    @21
    vy
    @24
    @26
    @27
    @21
    @24
    @26
    wa
    #
    @27
    @18
    @2
    cfv
    #
    cW
    c0g
    cfv
    #
    csn
    #
    wne
    #
    @21
    @30
    @27
    @25
    @31
    wcel
    #
    @34
    @30
    @0
    @18
    cB
    wss
    #
    @26
    @35
    @27
    wb
    @0
    @19
    @26
    simpll
    #
    @19
    @36
    @0
    @26
    @18
    cB
    pssss
    ad2antlr
    #
    @24
    @26
    simpr
    #
    @25
    cB
    @18
    @2
    cW
    @16
    obselocv
    syl3anc
    @30
    @25
    @33
    wcel
    wn
    #
    @35
    @34
    wi
    @30
    @25
    @32
    wne
    #
    @40
    @30
    @0
    @26
    @41
    @37
    @39
    @25
    cB
    cW
    @32
    @32
    eqid
    #
    obsne0
    syl2anc
    @25
    @32
    nelsn
    syl
    @35
    @40
    @34
    @25
    @31
    @33
    nelne1
    expcom
    syl
    sylbird
    @30
    @21
    @31
    @33
    @21
    wn
    @20
    @6
    wss
    #
    @20
    @6
    wceq
    #
    wi
    @30
    @31
    @33
    wceq
    #
    @20
    @6
    npss
    @30
    @43
    @44
    @45
    @30
    cW
    clmod
    wcel
    #
    @18
    @6
    wss
    #
    @43
    @0
    @46
    @19
    @26
    @0
    @11
    @46
    @13
    cW
    phllmod
    syl
    ad2antrr
    @30
    @18
    cB
    @6
    @38
    @0
    @12
    @19
    @26
    @15
    ad2antrr
    sstrd
    #
    @18
    cN
    @6
    cW
    @14
    obslbs.n
    lspssv
    syl2anc
    @44
    @20
    @2
    cfv
    #
    @6
    @2
    cfv
    #
    wceq
    @30
    @45
    @20
    @6
    @2
    fveq2
    @30
    @49
    @31
    @50
    @33
    @30
    @11
    @47
    @49
    @31
    wceq
    @0
    @11
    @19
    @26
    @13
    ad2antrr
    #
    @48
    @18
    cN
    @2
    @6
    cW
    @14
    @16
    obslbs.n
    ocvlsp
    syl2anc
    @30
    @11
    @50
    @33
    wceq
    @51
    @2
    @6
    cW
    @32
    @14
    @16
    @42
    ocv1
    syl
    eqeq12d
    syl5ib
    embantd
    syl5bi
    necon1ad
    syld
    expimpd
    exlimdv
    mpd
    ex
    alrimiv
    @17
    @9
    @12
    @23
    wa
    #
    @7
    @17
    @9
    @12
    @7
    @23
    w3a
    @52
    @7
    wa
    cB
    cJ
    cN
    @6
    cW
    vx
    @14
    obslbs.j
    obslbs.n
    islbs3
    @12
    @7
    @23
    3anan32
    syl6bb
    baibd
    syl12anc
    3bitr4rd
end
