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
include "sbc2rex.mm"
include "sbc4rex.mm"
include "2rexbii.mm"
include "bitri.mm"
include "sbcbii.mm"
include "3bitri.mm"
include "rabbii.mm"
include "caddc.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "syl5eqel.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "sbcrot3.mm"
include "sbcrot5.mm"
include "reseq1.mm"
include "sbccomieg.mm"
include "wss.mm"
include "wceq.mm"
include "wb.mm"
include "fzssp1.mm"
include "oveq2i.mm"
include "sseqtr4i.mm"
include "resabs1.mm"
include "dfsbcq.mm"
include "mp2b.mm"
include "cvv.mm"
include "vex.mm"
include "resex.mm"
include "fveq1.mm"
include "sbcco3g.mm"
include "ax-mp.mm"
include "elfz1end.mm"
include "sylib.mm"
include "fvres.mm"
include "3syl.mm"
include "syl5bb.mm"
include "sbcbidv.mm"
include "syl5bbr.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "biimpar.mm"
include "6rexfrabdioph.mm"
include "syl2anc.mm"
include "rexfrabdioph.mm"
include "syldan.mm"

theorem 7rexfrabdioph
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  assume rexfrabdioph.1: |- M = ( N + 1 )
  assume rexfrabdioph.2: |- L = ( M + 1 )
  assume rexfrabdioph.3: |- K = ( L + 1 )
  assume rexfrabdioph.4: |- J = ( K + 1 )
  assume rexfrabdioph.5: |- I = ( J + 1 )
  assume rexfrabdioph.6: |- H = ( I + 1 )
  assume rexfrabdioph.7: |- G = ( H + 1 )

  disjoint G t
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint G p
  disjoint G q
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint p t
  disjoint q t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint p u
  disjoint q u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint p v
  disjoint q v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint p w
  disjoint q w
  disjoint x y
  disjoint x z
  disjoint p x
  disjoint q x
  disjoint y z
  disjoint p y
  disjoint q y
  disjoint p z
  disjoint q z
  disjoint p q
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint H p
  disjoint H q
  disjoint I t
  disjoint I u
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint I p
  disjoint I q
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint J p
  disjoint J q
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint K p
  disjoint K q
  disjoint L t
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint L p
  disjoint L q
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint M p
  disjoint M q
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N p
  disjoint N q
  disjoint ph t
  disjoint G a
  disjoint G b
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
  disjoint H a
  disjoint H b
  disjoint I a
  disjoint I b
  disjoint J a
  disjoint J b
  disjoint K a
  disjoint K b
  disjoint L a
  disjoint L b
  disjoint M a
  disjoint M b
  disjoint N a
  disjoint N b
  disjoint a ph
  disjoint b ph
  assert |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... G ) ) | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. [. ( t ` L ) / w ]. [. ( t ` K ) / x ]. [. ( t ` J ) / y ]. [. ( t ` I ) / z ]. [. ( t ` H ) / p ]. [. ( t ` G ) / q ]. ph } e. ( Dioph ` G ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 E. y e. NN0 E. z e. NN0 E. p e. NN0 E. q e. NN0 ph } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    wph
    vq
    cG
    vt
    cv
    #
    cfv
    #
    wsbc
    vp
    cH
    @1
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
    #
    vx
    cK
    @1
    cfv
    #
    wsbc
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
    cG
    cfz
    co
    cmap
    co
    #
    crab
    #
    cG
    cdioph
    cfv
    #
    wcel
    #
    wph
    vq
    cn0
    wrex
    vp
    cn0
    wrex
    vz
    cn0
    wrex
    vy
    cn0
    wrex
    #
    vx
    cn0
    wrex
    vw
    cn0
    wrex
    #
    vv
    cM
    va
    cv
    #
    cfv
    #
    wsbc
    #
    vu
    @21
    @12
    cres
    #
    wsbc
    #
    va
    cn0
    c1
    cM
    cfz
    co
    #
    cmap
    co
    #
    crab
    #
    cM
    cdioph
    cfv
    #
    wcel
    @20
    vv
    cn0
    wrex
    vu
    cn0
    @12
    cmap
    co
    crab
    cN
    cdioph
    cfv
    wcel
    @0
    @18
    wa
    #
    @28
    wph
    vv
    @22
    wsbc
    #
    vu
    @24
    wsbc
    #
    vq
    cn0
    wrex
    vp
    cn0
    wrex
    vz
    cn0
    wrex
    vy
    cn0
    wrex
    #
    vx
    cn0
    wrex
    vw
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
    @31
    vq
    cn0
    wrex
    vp
    cn0
    wrex
    vz
    cn0
    wrex
    vy
    cn0
    wrex
    #
    vx
    cn0
    wrex
    vw
    cn0
    wrex
    #
    vu
    @24
    wsbc
    @36
    vu
    @24
    wsbc
    #
    vx
    cn0
    wrex
    vw
    cn0
    wrex
    @34
    @23
    @37
    vu
    @24
    @23
    @19
    vv
    @22
    wsbc
    #
    vx
    cn0
    wrex
    vw
    cn0
    wrex
    @37
    @19
    @22
    cn0
    cn0
    vv
    vw
    vx
    sbc2rex
    @39
    @36
    vw
    vx
    cn0
    cn0
    wph
    @22
    cn0
    cn0
    cn0
    vq
    cn0
    vv
    vy
    vz
    vp
    sbc4rex
    2rexbii
    bitri
    sbcbii
    @36
    @24
    cn0
    cn0
    vu
    vw
    vx
    sbc2rex
    @38
    @33
    vw
    vx
    cn0
    cn0
    @31
    @24
    cn0
    cn0
    cn0
    vq
    cn0
    vu
    vy
    vz
    vp
    sbc4rex
    2rexbii
    3bitri
    rabbii
    @30
    cM
    cn0
    wcel
    #
    @32
    vq
    @2
    wsbc
    vp
    @3
    wsbc
    vz
    @4
    wsbc
    vy
    @5
    wsbc
    #
    vx
    @7
    wsbc
    #
    vw
    @8
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
    @15
    crab
    #
    @17
    wcel
    #
    @35
    @29
    wcel
    @0
    @40
    @18
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
    nnnn0d
    adantr
    @0
    @47
    @18
    @0
    @46
    @16
    @17
    @0
    @45
    @14
    vt
    @15
    @45
    @9
    vv
    @22
    wsbc
    #
    vu
    @24
    wsbc
    #
    va
    @44
    wsbc
    #
    @0
    @14
    @51
    @43
    va
    @44
    @51
    @6
    vv
    @22
    wsbc
    #
    vx
    @7
    wsbc
    vw
    @8
    wsbc
    #
    vu
    @24
    wsbc
    @53
    vu
    @24
    wsbc
    #
    vx
    @7
    wsbc
    #
    vw
    @8
    wsbc
    @43
    @50
    @54
    vu
    @24
    @6
    @22
    @8
    @7
    vv
    vw
    vx
    sbcrot3
    sbcbii
    @53
    @24
    @8
    @7
    vu
    vw
    vx
    sbcrot3
    @56
    @42
    vw
    @8
    @55
    @41
    vx
    @7
    @55
    @31
    vq
    @2
    wsbc
    vp
    @3
    wsbc
    vz
    @4
    wsbc
    vy
    @5
    wsbc
    #
    vu
    @24
    wsbc
    @41
    @53
    @57
    vu
    @24
    wph
    @22
    @5
    @4
    @3
    vq
    @2
    vv
    vy
    vz
    vp
    sbcrot5
    sbcbii
    @31
    @24
    @5
    @4
    @3
    vq
    @2
    vu
    vy
    vz
    vp
    sbcrot5
    bitri
    sbcbii
    sbcbii
    3bitri
    sbcbii
    @52
    @50
    va
    @44
    wsbc
    #
    vu
    @44
    @12
    cres
    #
    wsbc
    #
    @0
    @14
    @50
    @44
    @24
    @59
    va
    vu
    @21
    @44
    @12
    reseq1
    sbccomieg
    @60
    @58
    vu
    @13
    wsbc
    #
    @0
    @14
    @12
    @26
    wss
    @59
    @13
    wceq
    @60
    @61
    wb
    @12
    c1
    @48
    cfz
    co
    @26
    c1
    cN
    fzssp1
    cM
    @48
    c1
    cfz
    rexfrabdioph.1
    oveq2i
    sseqtr4i
    @1
    @12
    @26
    resabs1
    @58
    vu
    @59
    @13
    dfsbcq
    mp2b
    @0
    @58
    @11
    vu
    @13
    @58
    @9
    vv
    cM
    @44
    cfv
    #
    wsbc
    #
    @0
    @11
    @44
    cvv
    wcel
    @58
    @63
    wb
    @1
    @26
    vt
    vex
    resex
    @9
    va
    vv
    @44
    @22
    @62
    cvv
    cM
    @21
    @44
    fveq1
    sbcco3g
    ax-mp
    @0
    cM
    @26
    wcel
    #
    @62
    @10
    wceq
    @63
    @11
    wb
    @0
    cM
    cn
    wcel
    @64
    @49
    cM
    elfz1end
    sylib
    cM
    @26
    @1
    fvres
    @9
    vv
    @62
    @10
    dfsbcq
    3syl
    syl5bb
    sbcbidv
    syl5bb
    syl5bb
    syl5bbr
    rabbidv
    eleq1d
    biimpar
    @32
    vy
    vz
    vp
    vx
    vw
    va
    vt
    cG
    cH
    cI
    cJ
    cK
    cL
    cM
    vq
    rexfrabdioph.2
    rexfrabdioph.3
    rexfrabdioph.4
    rexfrabdioph.5
    rexfrabdioph.6
    rexfrabdioph.7
    6rexfrabdioph
    syl2anc
    syl5eqel
    @20
    vv
    vu
    va
    cM
    cN
    rexfrabdioph.1
    rexfrabdioph
    syldan
end
