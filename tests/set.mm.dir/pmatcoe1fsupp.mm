include "cfn.mm"
include "wcel.mm"
include "crg.mm"
include "w3a.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cn0.mm"
include "wral.mm"
include "cxp.mm"
include "cco1.mm"
include "csn.mm"
include "ciun.mm"
include "cfsupp.mm"
include "cbs.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "cin.mm"
include "wrex.mm"
include "wss.mm"
include "cvv.mm"
include "wo.mm"
include "ssrab2.mm"
include "a1i.mm"
include "olcd.mm"
include "inss.mm"
include "syl.mm"
include "wa.mm"
include "xpfi.mm"
include "anidms.mm"
include "snfi.mm"
include "ralrimiva.mm"
include "jca.mm"
include "3ad2ant1.mm"
include "iunfi.mm"
include "infi.mm"
include "3syl.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elin.mm"
include "breq1.mm"
include "elrab.mm"
include "simprbi.mm"
include "simplbiim.mm"
include "rgen.mm"
include "fsuppmapnn0fiub0.mm"
include "imp.mm"
include "syl31anc.mm"
include "cop.mm"
include "opelxpi.mm"
include "df-ov.mm"
include "fveq2i.mm"
include "snid.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "eliuni.mm"
include "syl2anc.mm"
include "adantl.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "ad3antrrr.mm"
include "syl6eleqr.mm"
include "matecld.mm"
include "coe1fsupp.mm"
include "wb.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "elind.mm"
include "simplr.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "breq2.mm"
include "imbi12d.mm"
include "rspc2v.mm"
include "ex.mm"
include "com23.mm"
include "impancom.mm"
include "ralrimdvv.mm"
include "reximdva.mm"
include "mpd.mm"

theorem pmatcoe1fsupp
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cP: class P
  let cR: class R
  let vi: setvar i
  let vj: setvar j
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vs: setvar s
  let vv: setvar v
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  assume pmatcoe1fsupp.p: |- P = ( Poly1 ` R )
  assume pmatcoe1fsupp.c: |- C = ( N Mat P )
  assume pmatcoe1fsupp.b: |- B = ( Base ` C )
  assume pmatcoe1fsupp.0: |- .0. = ( 0g ` R )

  disjoint B i
  disjoint B j
  disjoint B s
  disjoint B x
  disjoint i j
  disjoint i s
  disjoint i x
  disjoint j s
  disjoint j x
  disjoint s x
  disjoint M i
  disjoint M j
  disjoint M s
  disjoint M x
  disjoint N i
  disjoint N j
  disjoint N s
  disjoint N x
  disjoint R i
  disjoint R j
  disjoint R s
  disjoint R x
  disjoint .0. i
  disjoint .0. j
  disjoint .0. s
  disjoint .0. x
  disjoint B v
  disjoint i v
  disjoint j v
  disjoint s v
  disjoint v x
  disjoint M u
  disjoint M w
  disjoint M z
  disjoint i u
  disjoint i w
  disjoint i z
  disjoint j u
  disjoint j w
  disjoint j z
  disjoint s u
  disjoint s w
  disjoint s z
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint w x
  disjoint w z
  disjoint x z
  disjoint M v
  disjoint v w
  disjoint v z
  disjoint N u
  disjoint N w
  disjoint N z
  disjoint N v
  disjoint R v
  disjoint R w
  disjoint R z
  disjoint .0. v
  disjoint .0. w
  disjoint .0. z
  assert |- ( ( N e. Fin /\ R e. Ring /\ M e. B ) -> E. s e. NN0 A. x e. NN0 ( s < x -> A. i e. N A. j e. N ( ( coe1 ` ( i M j ) ) ` x ) = .0. ) )

  proof
    cN
    cfn
    wcel
    #
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    w3a
    #
    vs
    cv
    #
    vz
    cv
    #
    clt
    wbr
    #
    @5
    vw
    cv
    #
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vz
    cn0
    wral
    vw
    vu
    cN
    cN
    cxp
    #
    vu
    cv
    #
    cM
    cfv
    #
    cco1
    cfv
    #
    csn
    #
    ciun
    #
    vv
    cv
    #
    c.0
    cfsupp
    wbr
    #
    vv
    cR
    cbs
    cfv
    #
    cn0
    cmap
    co
    #
    crab
    #
    cin
    #
    wral
    #
    vs
    cn0
    wrex
    #
    @4
    vx
    cv
    #
    clt
    wbr
    #
    @25
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cco1
    cfv
    #
    cfv
    #
    c.0
    wceq
    #
    vj
    cN
    wral
    vi
    cN
    wral
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    @3
    @22
    @20
    wss
    #
    @22
    cfn
    wcel
    #
    c.0
    cvv
    wcel
    #
    @7
    c.0
    cfsupp
    wbr
    #
    vw
    @22
    wral
    #
    @24
    @3
    @16
    @20
    wss
    #
    @21
    @20
    wss
    #
    wo
    @35
    @3
    @41
    @40
    @41
    @3
    @18
    vv
    @20
    ssrab2
    a1i
    olcd
    @16
    @21
    @20
    inss
    syl
    @3
    @11
    cfn
    wcel
    #
    @15
    cfn
    wcel
    #
    vu
    @11
    wral
    #
    wa
    #
    @16
    cfn
    wcel
    @36
    @0
    @1
    @45
    @2
    @0
    @42
    @44
    @0
    @42
    cN
    cN
    xpfi
    anidms
    @0
    @43
    vu
    @11
    @43
    @0
    @12
    @11
    wcel
    wa
    @14
    snfi
    a1i
    ralrimiva
    jca
    3ad2ant1
    vu
    @11
    @15
    iunfi
    @16
    @21
    infi
    3syl
    @37
    @3
    c.0
    cR
    c0g
    cfv
    #
    cvv
    pmatcoe1fsupp.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    @39
    @3
    @38
    vw
    @22
    @7
    @22
    wcel
    @7
    @16
    wcel
    @7
    @21
    wcel
    #
    @38
    @7
    @16
    @21
    elin
    @47
    @7
    @20
    wcel
    @38
    @18
    @38
    vv
    @7
    @20
    @17
    @7
    c.0
    cfsupp
    breq1
    elrab
    simprbi
    simplbiim
    rgen
    a1i
    @35
    @36
    @37
    w3a
    @39
    @24
    vz
    @19
    vw
    vs
    @22
    cvv
    c.0
    fsuppmapnn0fiub0
    imp
    syl31anc
    @3
    @23
    @34
    vs
    cn0
    @3
    @4
    cn0
    wcel
    #
    wa
    #
    @23
    @34
    @49
    @23
    wa
    #
    @33
    vx
    cn0
    @50
    @25
    cn0
    wcel
    #
    wa
    #
    @26
    @32
    vi
    vj
    cN
    cN
    @52
    @27
    cN
    wcel
    #
    @28
    cN
    wcel
    #
    wa
    #
    @26
    @32
    @50
    @51
    @55
    @26
    @32
    wi
    #
    wi
    #
    @49
    @51
    @23
    @57
    @49
    @51
    wa
    #
    @55
    @23
    @56
    @58
    @55
    @23
    @56
    wi
    #
    @58
    @55
    wa
    #
    @30
    @22
    wcel
    @51
    @59
    @60
    @16
    @21
    @30
    @55
    @30
    @16
    wcel
    #
    @58
    @55
    @27
    @28
    cop
    #
    @11
    wcel
    @30
    @62
    cM
    cfv
    #
    cco1
    cfv
    #
    csn
    #
    wcel
    #
    @61
    @27
    @28
    cN
    cN
    opelxpi
    @66
    @55
    @30
    @64
    @65
    @29
    @63
    cco1
    @27
    @28
    cM
    df-ov
    fveq2i
    @64
    @63
    cco1
    fvex
    snid
    eqeltri
    a1i
    vu
    @62
    @15
    @65
    @11
    @30
    @12
    @62
    wceq
    #
    @14
    @64
    @67
    @13
    @63
    cco1
    @12
    @62
    cM
    fveq2
    fveq2d
    sneqd
    eliuni
    syl2anc
    adantl
    @60
    @30
    @21
    wcel
    #
    @30
    @17
    @46
    cfsupp
    wbr
    #
    vv
    @20
    crab
    #
    wcel
    #
    @60
    @29
    cP
    cbs
    cfv
    #
    wcel
    @71
    @60
    cC
    cB
    cP
    @27
    @28
    @72
    cM
    cN
    pmatcoe1fsupp.c
    @72
    eqid
    #
    pmatcoe1fsupp.b
    @58
    @53
    @54
    simprl
    @58
    @53
    @54
    simprr
    @60
    cM
    cC
    cbs
    cfv
    #
    cB
    @3
    cM
    @74
    wcel
    #
    @48
    @51
    @55
    @2
    @0
    @75
    @1
    @2
    @75
    cB
    @74
    cM
    pmatcoe1fsupp.b
    eleq2i
    biimpi
    3ad2ant3
    ad3antrrr
    pmatcoe1fsupp.b
    syl6eleqr
    matecld
    @30
    @72
    cP
    cR
    vv
    @29
    @19
    @46
    @30
    eqid
    @73
    pmatcoe1fsupp.p
    @46
    eqid
    @19
    eqid
    coe1fsupp
    syl
    @3
    @68
    @71
    wb
    @48
    @51
    @55
    @3
    @21
    @70
    @30
    @3
    @18
    @69
    vv
    @20
    @3
    c.0
    @46
    @17
    cfsupp
    c.0
    @46
    wceq
    @3
    pmatcoe1fsupp.0
    a1i
    breq2d
    rabbidv
    eleq2d
    ad3antrrr
    mpbird
    elind
    @49
    @51
    @55
    simplr
    @10
    @56
    @6
    @5
    @30
    cfv
    #
    c.0
    wceq
    #
    wi
    vw
    vz
    @30
    @25
    @22
    cn0
    @7
    @30
    wceq
    #
    @9
    @77
    @6
    @78
    @8
    @76
    c.0
    @5
    @7
    @30
    fveq1
    eqeq1d
    imbi2d
    @5
    @25
    wceq
    #
    @6
    @26
    @77
    @32
    @5
    @25
    @4
    clt
    breq2
    @79
    @76
    @31
    c.0
    @5
    @25
    @30
    fveq2
    eqeq1d
    imbi12d
    rspc2v
    syl2anc
    ex
    com23
    impancom
    imp
    com23
    ralrimdvv
    ralrimiva
    ex
    reximdva
    mpd
end
