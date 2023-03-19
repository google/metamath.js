include "cv.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "wcel.mm"
include "crab.mm"
include "chash.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "cdm.mm"
include "ciedg.mm"
include "cun.mm"
include "elnelun.mm"
include "eqcomi.mm"
include "rabeqi.mm"
include "rabun2.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "cvv.mm"
include "cin.mm"
include "c0.mm"
include "fvexi.mm"
include "dmex.mm"
include "rab2ex.mm"
include "wnel.mm"
include "wss.mm"
include "ssrab2.mm"
include "ss2in.mm"
include "mp2an.mm"
include "elneldisj.mm"
include "sseq2i.mm"
include "ss0.mm"
include "sylbi.mm"
include "ax-mp.mm"
include "hashunx.mm"
include "mp3an.mm"
include "oveq12i.mm"
include "cxnn0.mm"
include "hashxnn0.mm"
include "a1i.mm"
include "xnn0add4d.mm"
include "cxr.mm"
include "xnn0xaddcl.mm"
include "xnn0xr.mm"
include "xaddcom.mm"
include "cc0.mm"
include "vtxdginducedm1lem4.mm"
include "oveq2d.mm"
include "xaddid1.mm"
include "syl6eq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "cbvrabv.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "vtxdginducedm1lem2.mm"
include "vtxdginducedm1lem3.mm"
include "rabbiia.mm"
include "eqeq1d.mm"
include "oveq1i.mm"
include "eldifi.mm"
include "eqid.mm"
include "vtxdgval.mm"
include "syl.mm"
include "cvtx.mm"
include "cop.mm"
include "difexg.mm"
include "syl5eqel.mm"
include "cres.mm"
include "resexg.mm"
include "opvtxfvi.mm"
include "eleq2i.mm"
include "sylbbr.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "rgen.mm"

theorem vtxdginducedm1
  let vv: setvar v
  let cP: class P
  let cS: class S
  let vi: setvar i
  let cE: class E
  let cG: class G
  let cI: class I
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let vl: setvar l
  let vk: setvar k
  let cW: class W
  assume vtxdginducedm1.v: |- V = ( Vtx ` G )
  assume vtxdginducedm1.e: |- E = ( iEdg ` G )
  assume vtxdginducedm1.k: |- K = ( V \ { N } )
  assume vtxdginducedm1.i: |- I = { i e. dom E | N e/ ( E ` i ) }
  assume vtxdginducedm1.p: |- P = ( E |` I )
  assume vtxdginducedm1.s: |- S = <. K , P >.
  assume vtxdginducedm1.j: |- J = { i e. dom E | N e. ( E ` i ) }

  disjoint E i
  disjoint N i
  disjoint E l
  disjoint J l
  disjoint l v
  disjoint J k
  disjoint N k
  disjoint i k
  disjoint V k
  disjoint W k
  disjoint E k
  disjoint k l
  disjoint G k
  disjoint I k
  disjoint S k
  disjoint k v
  assert |- A. v e. ( V \ { N } ) ( ( VtxDeg ` G ) ` v ) = ( ( ( VtxDeg ` S ) ` v ) +e ( # ` { l e. J | v e. ( E ` l ) } ) )

  proof
    vv
    cv
    #
    cG
    cvtxdg
    cfv
    cfv
    #
    @0
    cS
    cvtxdg
    cfv
    cfv
    #
    @0
    vl
    cv
    #
    cE
    cfv
    #
    wcel
    #
    vl
    cJ
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    wceq
    vv
    cV
    cN
    csn
    #
    cdif
    #
    @0
    @10
    wcel
    #
    @0
    vk
    cv
    #
    cE
    cfv
    #
    wcel
    #
    vk
    cE
    cdm
    #
    crab
    #
    chash
    cfv
    #
    @13
    @0
    csn
    #
    wceq
    #
    vk
    @15
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    @0
    @12
    cS
    ciedg
    cfv
    #
    cfv
    #
    wcel
    #
    vk
    @23
    cdm
    #
    crab
    #
    chash
    cfv
    #
    @24
    @18
    wceq
    #
    vk
    @26
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    @7
    cxad
    co
    #
    @1
    @8
    @11
    @22
    @14
    vk
    cI
    crab
    #
    chash
    cfv
    #
    @19
    vk
    cI
    crab
    #
    chash
    cfv
    #
    cxad
    co
    #
    @7
    cxad
    co
    #
    @33
    @11
    @22
    @14
    vk
    cJ
    crab
    #
    chash
    cfv
    #
    @35
    cxad
    co
    #
    @19
    vk
    cJ
    crab
    #
    chash
    cfv
    #
    @37
    cxad
    co
    #
    cxad
    co
    #
    @39
    @17
    @42
    @21
    @45
    cxad
    @17
    @40
    @34
    cun
    #
    chash
    cfv
    #
    @42
    @16
    @47
    chash
    @16
    @14
    vk
    cJ
    cI
    cun
    #
    crab
    @47
    @14
    vk
    @15
    @49
    @49
    @15
    @15
    cN
    vi
    cv
    cE
    cfv
    #
    cJ
    cI
    vi
    vtxdginducedm1.j
    vtxdginducedm1.i
    elnelun
    eqcomi
    #
    rabeqi
    @14
    vk
    cJ
    cI
    rabun2
    eqtri
    fveq2i
    @40
    cvv
    wcel
    #
    @34
    cvv
    wcel
    #
    @40
    @34
    cin
    #
    c0
    wceq
    #
    @48
    @42
    wceq
    @14
    cN
    @50
    wcel
    #
    vk
    vi
    @15
    cJ
    vtxdginducedm1.j
    cE
    cE
    cG
    ciedg
    vtxdginducedm1.e
    fvexi
    #
    dmex
    #
    rab2ex
    #
    @14
    cN
    @50
    wnel
    #
    vk
    vi
    @15
    cI
    vtxdginducedm1.i
    @58
    rab2ex
    #
    @54
    cJ
    cI
    cin
    #
    wss
    #
    @55
    @40
    cJ
    wss
    @34
    cI
    wss
    @63
    @14
    vk
    cJ
    ssrab2
    @14
    vk
    cI
    ssrab2
    @40
    cJ
    @34
    cI
    ss2in
    mp2an
    @63
    @54
    c0
    wss
    @55
    @62
    c0
    @54
    @15
    cN
    @50
    cJ
    cI
    vi
    vtxdginducedm1.j
    vtxdginducedm1.i
    elneldisj
    #
    sseq2i
    @54
    ss0
    sylbi
    ax-mp
    @40
    @34
    cvv
    cvv
    hashunx
    mp3an
    eqtri
    @21
    @43
    @36
    cun
    #
    chash
    cfv
    #
    @45
    @20
    @65
    chash
    @20
    @19
    vk
    @49
    crab
    @65
    @19
    vk
    @15
    @49
    @51
    rabeqi
    @19
    vk
    cJ
    cI
    rabun2
    eqtri
    fveq2i
    @43
    cvv
    wcel
    #
    @36
    cvv
    wcel
    #
    @43
    @36
    cin
    #
    c0
    wceq
    #
    @66
    @45
    wceq
    @19
    @56
    vk
    vi
    @15
    cJ
    vtxdginducedm1.j
    @58
    rab2ex
    #
    @19
    @60
    vk
    vi
    @15
    cI
    vtxdginducedm1.i
    @58
    rab2ex
    #
    @69
    @62
    wss
    #
    @70
    @43
    cJ
    wss
    @36
    cI
    wss
    @73
    @19
    vk
    cJ
    ssrab2
    @19
    vk
    cI
    ssrab2
    @43
    cJ
    @36
    cI
    ss2in
    mp2an
    @73
    @69
    c0
    wss
    @70
    @62
    c0
    @69
    @64
    sseq2i
    @69
    ss0
    sylbi
    ax-mp
    @43
    @36
    cvv
    cvv
    hashunx
    mp3an
    eqtri
    oveq12i
    @11
    @46
    @41
    @44
    cxad
    co
    #
    @38
    cxad
    co
    #
    @39
    @11
    @41
    @35
    @44
    @37
    @41
    cxnn0
    wcel
    #
    @11
    @52
    @76
    @59
    @40
    cvv
    hashxnn0
    ax-mp
    #
    a1i
    @35
    cxnn0
    wcel
    #
    @11
    @53
    @78
    @61
    @34
    cvv
    hashxnn0
    ax-mp
    #
    a1i
    @44
    cxnn0
    wcel
    #
    @11
    @67
    @80
    @71
    @43
    cvv
    hashxnn0
    ax-mp
    #
    a1i
    @37
    cxnn0
    wcel
    #
    @11
    @68
    @82
    @72
    @36
    cvv
    hashxnn0
    ax-mp
    #
    a1i
    xnn0add4d
    @11
    @75
    @38
    @74
    cxad
    co
    #
    @39
    @74
    cxr
    wcel
    #
    @38
    cxr
    wcel
    #
    @75
    @84
    wceq
    @74
    cxnn0
    wcel
    #
    @85
    @76
    @80
    @87
    @77
    @81
    @41
    @44
    xnn0xaddcl
    mp2an
    @74
    xnn0xr
    ax-mp
    @38
    cxnn0
    wcel
    #
    @86
    @78
    @82
    @88
    @79
    @83
    @35
    @37
    xnn0xaddcl
    mp2an
    @38
    xnn0xr
    ax-mp
    @74
    @38
    xaddcom
    mp2an
    @11
    @74
    @7
    @38
    cxad
    @11
    @74
    @41
    @7
    @11
    @74
    @41
    cc0
    cxad
    co
    #
    @41
    @11
    @44
    cc0
    @41
    cxad
    cP
    cS
    vi
    vk
    cE
    cG
    cI
    cJ
    cK
    cN
    cV
    @0
    vtxdginducedm1.v
    vtxdginducedm1.e
    vtxdginducedm1.k
    vtxdginducedm1.i
    vtxdginducedm1.p
    vtxdginducedm1.s
    vtxdginducedm1.j
    vtxdginducedm1lem4
    oveq2d
    @41
    cxr
    wcel
    #
    @89
    @41
    wceq
    @76
    @90
    @77
    @41
    xnn0xr
    ax-mp
    @41
    xaddid1
    ax-mp
    syl6eq
    @40
    @6
    chash
    @14
    @5
    vk
    vl
    cJ
    @12
    @3
    wceq
    @13
    @4
    @0
    @12
    @3
    cE
    fveq2
    eleq2d
    cbvrabv
    fveq2i
    syl6eq
    oveq2d
    syl5eq
    eqtrd
    syl5eq
    @38
    @32
    @7
    cxad
    @32
    @38
    @28
    @35
    @31
    @37
    cxad
    @27
    @34
    chash
    @27
    @25
    vk
    cI
    crab
    @34
    @25
    vk
    @26
    cI
    cP
    cS
    vi
    cE
    cG
    cI
    cK
    cN
    cV
    vtxdginducedm1.v
    vtxdginducedm1.e
    vtxdginducedm1.k
    vtxdginducedm1.i
    vtxdginducedm1.p
    vtxdginducedm1.s
    vtxdginducedm1lem2
    #
    rabeqi
    @25
    @14
    vk
    cI
    @12
    cI
    wcel
    #
    @24
    @13
    @0
    cP
    cS
    vi
    cE
    cG
    @12
    cI
    cK
    cN
    cV
    vtxdginducedm1.v
    vtxdginducedm1.e
    vtxdginducedm1.k
    vtxdginducedm1.i
    vtxdginducedm1.p
    vtxdginducedm1.s
    vtxdginducedm1lem3
    #
    eleq2d
    rabbiia
    eqtri
    fveq2i
    @30
    @36
    chash
    @30
    @29
    vk
    cI
    crab
    @36
    @29
    vk
    @26
    cI
    @91
    rabeqi
    @29
    @19
    vk
    cI
    @92
    @24
    @13
    @18
    @93
    eqeq1d
    rabbiia
    eqtri
    fveq2i
    oveq12i
    eqcomi
    oveq1i
    syl6eq
    @11
    @0
    cV
    wcel
    @1
    @22
    wceq
    @0
    cV
    @9
    eldifi
    vk
    @15
    @0
    cG
    cE
    cV
    vtxdginducedm1.v
    vtxdginducedm1.e
    @15
    eqid
    vtxdgval
    syl
    @11
    @2
    @32
    @7
    cxad
    @11
    @0
    cS
    cvtx
    cfv
    #
    wcel
    #
    @2
    @32
    wceq
    @95
    @0
    cK
    wcel
    @11
    @94
    cK
    @0
    @94
    cK
    cP
    cop
    #
    cvtx
    cfv
    cK
    cS
    @96
    cvtx
    vtxdginducedm1.s
    fveq2i
    cP
    cK
    cV
    cvv
    wcel
    #
    cK
    cvv
    wcel
    cV
    cG
    cvtx
    vtxdginducedm1.v
    fvexi
    @97
    cK
    @10
    cvv
    vtxdginducedm1.k
    cV
    @9
    cvv
    difexg
    syl5eqel
    ax-mp
    cE
    cvv
    wcel
    #
    cP
    cvv
    wcel
    @57
    @98
    cP
    cE
    cI
    cres
    cvv
    vtxdginducedm1.p
    cE
    cI
    cvv
    resexg
    syl5eqel
    ax-mp
    opvtxfvi
    eqtri
    eleq2i
    cK
    @10
    @0
    vtxdginducedm1.k
    eleq2i
    sylbbr
    vk
    @26
    @0
    cS
    @23
    @94
    @94
    eqid
    @23
    eqid
    @26
    eqid
    vtxdgval
    syl
    oveq1d
    3eqtr4d
    rgen
end
