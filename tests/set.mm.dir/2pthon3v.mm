include "cuhgr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "cv.mm"
include "cspthson.mm"
include "cfv.mm"
include "co.mm"
include "wbr.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "wex.mm"
include "ciedg.mm"
include "cdm.mm"
include "wrex.mm"
include "wb.mm"
include "crn.mm"
include "cedg.mm"
include "edgval.mm"
include "eqtri.mm"
include "eleq2i.mm"
include "wfn.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "eqid.mm"
include "uhgrf.mm"
include "ffnd.mm"
include "fvelrnb.mm"
include "syl.mm"
include "syl5bb.mm"
include "anbi12d.mm"
include "adantr.mm"
include "reeanv.mm"
include "syl6bbr.mm"
include "cs2.mm"
include "cvv.mm"
include "cs3.mm"
include "cs1.mm"
include "cconcat.mm"
include "df-s2.mm"
include "ovexi.mm"
include "df-s3.mm"
include "pm3.2i.mm"
include "simp-4r.mm"
include "3simpb.mm"
include "ad3antlr.mm"
include "wss.mm"
include "eqimss2.mm"
include "anim12i.mm"
include "adantl.mm"
include "wi.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi1d.mm"
include "eqtr2.mm"
include "wo.mm"
include "3simpa.mm"
include "3simpc.mm"
include "preq12bg.mm"
include "syl2anc.mm"
include "eqneqall.mm"
include "com12.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "jaoi.mm"
include "syl6bi.mm"
include "com23.mm"
include "imp.mm"
include "2a1.mm"
include "pm2.61ine.mm"
include "simplr2.mm"
include "2pthond.mm"
include "s2len.mm"
include "jctir.mm"
include "breq12.mm"
include "spc2egv.mm"
include "mpsyl.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "3impia.mm"

theorem 2pthon3v
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cV: class V
  let vp: setvar p
  let vi: setvar i
  let vj: setvar j
  assume 2pthon3v.v: |- V = ( Vtx ` G )
  assume 2pthon3v.e: |- E = ( Edg ` G )

  disjoint A f
  disjoint A p
  disjoint f p
  disjoint B f
  disjoint B p
  disjoint C f
  disjoint C p
  disjoint G f
  disjoint G p
  disjoint A i
  disjoint A j
  disjoint f i
  disjoint f j
  disjoint i j
  disjoint i p
  disjoint j p
  disjoint B i
  disjoint B j
  disjoint C i
  disjoint C j
  disjoint G i
  disjoint G j
  disjoint V i
  disjoint V j
  assert |- ( ( ( G e. UHGraph /\ ( A e. V /\ B e. V /\ C e. V ) ) /\ ( A =/= B /\ A =/= C /\ B =/= C ) /\ ( { A , B } e. E /\ { B , C } e. E ) ) -> E. f E. p ( f ( A ( SPathsOn ` G ) C ) p /\ ( # ` f ) = 2 ) )

  proof
    cG
    cuhgr
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    w3a
    #
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    cB
    cC
    cpr
    #
    cE
    wcel
    #
    wa
    #
    vf
    cv
    #
    vp
    cv
    #
    cA
    cC
    cG
    cspthson
    cfv
    co
    #
    wbr
    #
    @15
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    vp
    wex
    vf
    wex
    #
    @5
    @9
    wa
    #
    @14
    vi
    cv
    #
    cG
    ciedg
    cfv
    #
    cfv
    #
    @10
    wceq
    #
    vj
    cv
    #
    @25
    cfv
    #
    @12
    wceq
    #
    wa
    #
    vj
    @25
    cdm
    #
    wrex
    vi
    @32
    wrex
    #
    @22
    @23
    @14
    @27
    vi
    @32
    wrex
    #
    @30
    vj
    @32
    wrex
    #
    wa
    #
    @33
    @5
    @14
    @36
    wb
    #
    @9
    @0
    @37
    @4
    @0
    @11
    @34
    @13
    @35
    @11
    @10
    @25
    crn
    #
    wcel
    #
    @0
    @34
    cE
    @38
    @10
    cE
    cG
    cedg
    cfv
    @38
    2pthon3v.e
    cG
    edgval
    eqtri
    #
    eleq2i
    @0
    @25
    @32
    wfn
    #
    @39
    @34
    wb
    @0
    @32
    cV
    cpw
    c0
    csn
    cdif
    @25
    @25
    cG
    cV
    2pthon3v.v
    @25
    eqid
    #
    uhgrf
    ffnd
    #
    vi
    @32
    @10
    @25
    fvelrnb
    syl
    syl5bb
    @13
    @12
    @38
    wcel
    #
    @0
    @35
    cE
    @38
    @12
    @40
    eleq2i
    @0
    @41
    @44
    @35
    wb
    @43
    vj
    @32
    @12
    @25
    fvelrnb
    syl
    syl5bb
    anbi12d
    adantr
    adantr
    @27
    @30
    vi
    vj
    @32
    @32
    reeanv
    syl6bbr
    @23
    @31
    @22
    vi
    vj
    @32
    @32
    @23
    @24
    @32
    wcel
    @28
    @32
    wcel
    wa
    #
    wa
    #
    @31
    @22
    @24
    @28
    cs2
    #
    cvv
    wcel
    #
    cA
    cB
    cC
    cs3
    #
    cvv
    wcel
    #
    wa
    @46
    @31
    wa
    #
    @47
    @49
    @17
    wbr
    #
    @47
    chash
    cfv
    #
    c2
    wceq
    #
    wa
    #
    @22
    @48
    @50
    @47
    @24
    cs1
    @28
    cs1
    cconcat
    @24
    @28
    df-s2
    ovexi
    @49
    cA
    cB
    cs2
    cC
    cs1
    cconcat
    cA
    cB
    cC
    df-s3
    ovexi
    pm3.2i
    @51
    @52
    @54
    @51
    cA
    cB
    cC
    @49
    @47
    cG
    @25
    @24
    @28
    cV
    @49
    eqid
    @47
    eqid
    @0
    @4
    @9
    @45
    @31
    simp-4r
    @9
    @6
    @8
    wa
    @5
    @45
    @31
    @6
    @7
    @8
    3simpb
    ad3antlr
    @31
    @10
    @26
    wss
    #
    @12
    @29
    wss
    #
    wa
    @46
    @27
    @56
    @30
    @57
    @10
    @26
    eqimss2
    @12
    @29
    eqimss2
    anim12i
    adantl
    2pthon3v.v
    @42
    @46
    @31
    @24
    @28
    wne
    #
    @23
    @31
    @58
    wi
    #
    @45
    @23
    @59
    wi
    @24
    @28
    @24
    @28
    wceq
    #
    @31
    @23
    @58
    @60
    @31
    @29
    @10
    wceq
    #
    @30
    wa
    #
    @23
    @58
    wi
    #
    @60
    @27
    @61
    @30
    @60
    @26
    @29
    @10
    @24
    @28
    @25
    fveq2
    eqeq1d
    anbi1d
    @62
    @10
    @12
    wceq
    #
    @63
    @29
    @10
    @12
    eqtr2
    @23
    @64
    @58
    @5
    @9
    @64
    @58
    wi
    #
    @4
    @9
    @65
    wi
    @0
    @4
    @64
    @9
    @58
    @4
    @64
    cA
    cB
    wceq
    #
    cB
    cC
    wceq
    #
    wa
    #
    cA
    cC
    wceq
    #
    cB
    cB
    wceq
    #
    wa
    #
    wo
    #
    @9
    @58
    wi
    #
    @4
    @1
    @2
    wa
    @2
    @3
    wa
    @64
    @72
    wb
    @1
    @2
    @3
    3simpa
    @1
    @2
    @3
    3simpc
    cA
    cB
    cB
    cC
    cV
    cV
    cV
    cV
    preq12bg
    syl2anc
    @68
    @73
    @71
    @66
    @73
    @67
    @9
    @66
    @58
    @6
    @7
    @66
    @58
    wi
    @8
    @66
    @6
    @58
    @58
    cA
    cB
    eqneqall
    com12
    3ad2ant1
    com12
    adantr
    @69
    @73
    @70
    @9
    @69
    @58
    @7
    @6
    @69
    @58
    wi
    @8
    @69
    @7
    @58
    @58
    cA
    cC
    eqneqall
    com12
    3ad2ant2
    com12
    adantr
    jaoi
    syl6bi
    com23
    adantl
    imp
    com12
    syl
    syl6bi
    com23
    @58
    @23
    @31
    2a1
    pm2.61ine
    adantr
    imp
    @46
    @7
    @31
    @6
    @7
    @8
    @5
    @45
    simplr2
    adantr
    2pthond
    @24
    @28
    s2len
    jctir
    @21
    @55
    vf
    vp
    @47
    @49
    cvv
    cvv
    @15
    @47
    wceq
    #
    @16
    @49
    wceq
    #
    wa
    @18
    @52
    @20
    @54
    @15
    @47
    @16
    @49
    @17
    breq12
    @74
    @20
    @54
    wb
    @75
    @74
    @19
    @53
    c2
    @15
    @47
    chash
    fveq2
    eqeq1d
    adantr
    anbi12d
    spc2egv
    mpsyl
    ex
    rexlimdvva
    sylbid
    3impia
end
