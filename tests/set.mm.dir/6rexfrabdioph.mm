include "cn0.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "wsbc.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "cmap.mm"
include "crab.mm"
include "cdioph.mm"
include "wrex.mm"
include "wa.mm"
include "sbc4rex.mm"
include "sbcbii.mm"
include "bitri.mm"
include "rabbii.mm"
include "caddc.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "syl5eqel.mm"
include "peano2nnd.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "sbcrot5.mm"
include "reseq1.mm"
include "sbccomieg.mm"
include "wss.mm"
include "wceq.mm"
include "wb.mm"
include "fzssp1.mm"
include "oveq2i.mm"
include "sseqtr4i.mm"
include "sstri.mm"
include "resabs1.mm"
include "dfsbcq.mm"
include "mp2b.mm"
include "fveq1.mm"
include "elfz1end.mm"
include "sylib.mm"
include "sseldi.mm"
include "fvres.mm"
include "3syl.mm"
include "cvv.mm"
include "vex.mm"
include "resex.mm"
include "sbcco3g.mm"
include "ax-mp.mm"
include "syl5bb.mm"
include "sbcbidv.mm"
include "bitrd.mm"
include "syl5bbr.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "biimpar.mm"
include "4rexfrabdioph.mm"
include "syl2anc.mm"
include "2rexfrabdioph.mm"
include "syldan.mm"

theorem 6rexfrabdioph
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let vp: setvar p
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vq: setvar q
  assume rexfrabdioph.1: |- M = ( N + 1 )
  assume rexfrabdioph.2: |- L = ( M + 1 )
  assume rexfrabdioph.3: |- K = ( L + 1 )
  assume rexfrabdioph.4: |- J = ( K + 1 )
  assume rexfrabdioph.5: |- I = ( J + 1 )
  assume rexfrabdioph.6: |- H = ( I + 1 )

  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint p t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint p u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint p v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint p w
  disjoint x y
  disjoint x z
  disjoint p x
  disjoint y z
  disjoint p y
  disjoint p z
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint H p
  disjoint I t
  disjoint I u
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint I p
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint J p
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint K p
  disjoint L t
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint L p
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint M p
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N p
  disjoint ph t
  disjoint G a
  disjoint G b
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint G p
  disjoint G q
  disjoint a b
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a p
  disjoint a q
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b p
  disjoint b q
  disjoint q t
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint p q
  disjoint H a
  disjoint H b
  disjoint H q
  disjoint I a
  disjoint I b
  disjoint I q
  disjoint J a
  disjoint J b
  disjoint J q
  disjoint K a
  disjoint K b
  disjoint K q
  disjoint L a
  disjoint L b
  disjoint L q
  disjoint M a
  disjoint M b
  disjoint M q
  disjoint N a
  disjoint N b
  disjoint N q
  disjoint a ph
  disjoint b ph
  assert |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... H ) ) | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. [. ( t ` L ) / w ]. [. ( t ` K ) / x ]. [. ( t ` J ) / y ]. [. ( t ` I ) / z ]. [. ( t ` H ) / p ]. ph } e. ( Dioph ` H ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 E. y e. NN0 E. z e. NN0 E. p e. NN0 ph } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    wph
    vp
    cH
    vt
    cv
    #
    cfv
    #
    wsbc
    vz
    cI
    @1
    cfv
    #
    wsbc
    vy
    cJ
    @1
    cfv
    #
    wsbc
    vx
    cK
    @1
    cfv
    #
    wsbc
    #
    vw
    cL
    @1
    cfv
    #
    wsbc
    #
    vv
    cM
    @1
    cfv
    #
    wsbc
    #
    vu
    @1
    c1
    cN
    cfz
    co
    #
    cres
    #
    wsbc
    #
    vt
    cn0
    c1
    cH
    cfz
    co
    cmap
    co
    #
    crab
    #
    cH
    cdioph
    cfv
    #
    wcel
    #
    wph
    vp
    cn0
    wrex
    vz
    cn0
    wrex
    vy
    cn0
    wrex
    vx
    cn0
    wrex
    #
    vw
    cL
    va
    cv
    #
    cfv
    #
    wsbc
    #
    vv
    cM
    @19
    cfv
    #
    wsbc
    #
    vu
    @19
    @11
    cres
    #
    wsbc
    #
    va
    cn0
    c1
    cL
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    cL
    cdioph
    cfv
    #
    wcel
    @18
    vw
    cn0
    wrex
    vv
    cn0
    wrex
    vu
    cn0
    @11
    cmap
    co
    crab
    cN
    cdioph
    cfv
    wcel
    @0
    @17
    wa
    #
    @28
    wph
    vw
    @20
    wsbc
    #
    vv
    @22
    wsbc
    #
    vu
    @24
    wsbc
    #
    vp
    cn0
    wrex
    vz
    cn0
    wrex
    vy
    cn0
    wrex
    vx
    cn0
    wrex
    #
    va
    @27
    crab
    #
    @29
    @25
    @34
    va
    @27
    @25
    @32
    vp
    cn0
    wrex
    vz
    cn0
    wrex
    vy
    cn0
    wrex
    vx
    cn0
    wrex
    #
    vu
    @24
    wsbc
    @34
    @23
    @36
    vu
    @24
    @23
    @31
    vp
    cn0
    wrex
    vz
    cn0
    wrex
    vy
    cn0
    wrex
    vx
    cn0
    wrex
    #
    vv
    @22
    wsbc
    @36
    @21
    @37
    vv
    @22
    wph
    @20
    cn0
    cn0
    cn0
    vp
    cn0
    vw
    vx
    vy
    vz
    sbc4rex
    sbcbii
    @31
    @22
    cn0
    cn0
    cn0
    vp
    cn0
    vv
    vx
    vy
    vz
    sbc4rex
    bitri
    sbcbii
    @32
    @24
    cn0
    cn0
    cn0
    vp
    cn0
    vu
    vx
    vy
    vz
    sbc4rex
    bitri
    rabbii
    @30
    cL
    cn0
    wcel
    #
    @33
    vp
    @2
    wsbc
    vz
    @3
    wsbc
    vy
    @4
    wsbc
    vx
    @5
    wsbc
    #
    va
    @1
    @26
    cres
    #
    wsbc
    #
    vt
    @14
    crab
    #
    @16
    wcel
    #
    @35
    @29
    wcel
    @0
    @38
    @17
    @0
    cL
    @0
    cL
    cM
    c1
    caddc
    co
    #
    cn
    rexfrabdioph.2
    @0
    cM
    @0
    cM
    cN
    c1
    caddc
    co
    #
    cn
    rexfrabdioph.1
    cN
    nn0p1nn
    syl5eqel
    #
    peano2nnd
    syl5eqel
    #
    nnnn0d
    adantr
    @0
    @43
    @17
    @0
    @42
    @15
    @16
    @0
    @41
    @13
    vt
    @14
    @41
    @6
    vw
    @20
    wsbc
    #
    vv
    @22
    wsbc
    #
    vu
    @24
    wsbc
    #
    va
    @40
    wsbc
    #
    @0
    @13
    @50
    @39
    va
    @40
    @50
    @32
    vp
    @2
    wsbc
    vz
    @3
    wsbc
    vy
    @4
    wsbc
    vx
    @5
    wsbc
    #
    vu
    @24
    wsbc
    @39
    @49
    @52
    vu
    @24
    @49
    @31
    vp
    @2
    wsbc
    vz
    @3
    wsbc
    vy
    @4
    wsbc
    vx
    @5
    wsbc
    #
    vv
    @22
    wsbc
    @52
    @48
    @53
    vv
    @22
    wph
    @20
    @5
    @4
    @3
    vp
    @2
    vw
    vx
    vy
    vz
    sbcrot5
    sbcbii
    @31
    @22
    @5
    @4
    @3
    vp
    @2
    vv
    vx
    vy
    vz
    sbcrot5
    bitri
    sbcbii
    @32
    @24
    @5
    @4
    @3
    vp
    @2
    vu
    vx
    vy
    vz
    sbcrot5
    bitri
    sbcbii
    @51
    @49
    va
    @40
    wsbc
    #
    vu
    @40
    @11
    cres
    #
    wsbc
    #
    @0
    @13
    @49
    @40
    @24
    @55
    va
    vu
    @19
    @40
    @11
    reseq1
    sbccomieg
    @56
    @54
    vu
    @12
    wsbc
    #
    @0
    @13
    @11
    @26
    wss
    @55
    @12
    wceq
    @56
    @57
    wb
    @11
    c1
    cM
    cfz
    co
    #
    @26
    @11
    c1
    @45
    cfz
    co
    @58
    c1
    cN
    fzssp1
    cM
    @45
    c1
    cfz
    rexfrabdioph.1
    oveq2i
    sseqtr4i
    @58
    c1
    @44
    cfz
    co
    @26
    c1
    cM
    fzssp1
    cL
    @44
    c1
    cfz
    rexfrabdioph.2
    oveq2i
    sseqtr4i
    #
    sstri
    @1
    @11
    @26
    resabs1
    @54
    vu
    @55
    @12
    dfsbcq
    mp2b
    @0
    @54
    @10
    vu
    @12
    @54
    @48
    va
    @40
    wsbc
    #
    vv
    cM
    @40
    cfv
    #
    wsbc
    #
    @0
    @10
    @48
    @40
    @22
    @61
    va
    vv
    cM
    @19
    @40
    fveq1
    sbccomieg
    @0
    @62
    @60
    vv
    @9
    wsbc
    #
    @10
    @0
    cM
    @26
    wcel
    @61
    @9
    wceq
    @62
    @63
    wb
    @0
    @58
    @26
    cM
    @59
    @0
    cM
    cn
    wcel
    cM
    @58
    wcel
    @46
    cM
    elfz1end
    sylib
    sseldi
    cM
    @26
    @1
    fvres
    @60
    vv
    @61
    @9
    dfsbcq
    3syl
    @0
    @60
    @8
    vv
    @9
    @60
    @6
    vw
    cL
    @40
    cfv
    #
    wsbc
    #
    @0
    @8
    @40
    cvv
    wcel
    @60
    @65
    wb
    @1
    @26
    vt
    vex
    resex
    @6
    va
    vw
    @40
    @20
    @64
    cvv
    cL
    @19
    @40
    fveq1
    sbcco3g
    ax-mp
    @0
    cL
    @26
    wcel
    #
    @64
    @7
    wceq
    @65
    @8
    wb
    @0
    cL
    cn
    wcel
    @66
    @47
    cL
    elfz1end
    sylib
    cL
    @26
    @1
    fvres
    @6
    vw
    @64
    @7
    dfsbcq
    3syl
    syl5bb
    sbcbidv
    bitrd
    syl5bb
    sbcbidv
    syl5bb
    syl5bb
    syl5bbr
    rabbidv
    eleq1d
    biimpar
    @33
    vz
    vp
    vy
    vx
    va
    vt
    cH
    cI
    cJ
    cK
    cL
    rexfrabdioph.3
    rexfrabdioph.4
    rexfrabdioph.5
    rexfrabdioph.6
    4rexfrabdioph
    syl2anc
    syl5eqel
    @18
    vw
    vv
    vu
    va
    cL
    cM
    cN
    rexfrabdioph.1
    rexfrabdioph.2
    2rexfrabdioph
    syldan
end
