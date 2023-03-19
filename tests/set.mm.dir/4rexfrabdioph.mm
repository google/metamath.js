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
include "2sbcrex.mm"
include "rexbii.mm"
include "bitri.mm"
include "sbcbii.mm"
include "sbc2rex.mm"
include "rabbii.mm"
include "caddc.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "syl5eqel.mm"
include "peano2nnd.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "sbcrot3.mm"
include "bitr3i.mm"
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
include "rabbidv.mm"
include "eleq1d.mm"
include "biimpar.mm"
include "2rexfrabdioph.mm"
include "syl2anc.mm"
include "syldan.mm"

theorem 4rexfrabdioph
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let vp: setvar p
  let vq: setvar q
  let cH: class H
  let cI: class I
  assume rexfrabdioph.1: |- M = ( N + 1 )
  assume rexfrabdioph.2: |- L = ( M + 1 )
  assume rexfrabdioph.3: |- K = ( L + 1 )
  assume rexfrabdioph.4: |- J = ( K + 1 )

  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint L t
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint N x
  disjoint N y
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
  disjoint t z
  disjoint p t
  disjoint q t
  disjoint u z
  disjoint p u
  disjoint q u
  disjoint v z
  disjoint p v
  disjoint q v
  disjoint w z
  disjoint p w
  disjoint q w
  disjoint x z
  disjoint p x
  disjoint q x
  disjoint y z
  disjoint p y
  disjoint q y
  disjoint p z
  disjoint q z
  disjoint p q
  disjoint H a
  disjoint H b
  disjoint H t
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint H p
  disjoint H q
  disjoint I a
  disjoint I b
  disjoint I t
  disjoint I u
  disjoint I v
  disjoint I w
  disjoint I x
  disjoint I y
  disjoint I z
  disjoint I p
  disjoint I q
  disjoint J a
  disjoint J b
  disjoint J z
  disjoint J p
  disjoint J q
  disjoint K a
  disjoint K b
  disjoint K z
  disjoint K p
  disjoint K q
  disjoint L a
  disjoint L b
  disjoint L z
  disjoint L p
  disjoint L q
  disjoint M a
  disjoint M b
  disjoint M z
  disjoint M p
  disjoint M q
  disjoint N a
  disjoint N b
  disjoint N z
  disjoint N p
  disjoint N q
  disjoint a ph
  disjoint b ph
  assert |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... J ) ) | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. [. ( t ` L ) / w ]. [. ( t ` K ) / x ]. [. ( t ` J ) / y ]. ph } e. ( Dioph ` J ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 E. y e. NN0 ph } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    wph
    vy
    cJ
    vt
    cv
    #
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
    cJ
    cfz
    co
    cmap
    co
    #
    crab
    #
    cJ
    cdioph
    cfv
    #
    wcel
    #
    wph
    vy
    cn0
    wrex
    #
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
    vv
    cM
    @19
    cfv
    #
    wsbc
    #
    vu
    @19
    @10
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
    @10
    cmap
    co
    crab
    cN
    cdioph
    cfv
    wcel
    @0
    @16
    wa
    #
    @27
    wph
    vw
    @20
    wsbc
    vv
    @21
    wsbc
    #
    vu
    @23
    wsbc
    #
    vy
    cn0
    wrex
    vx
    cn0
    wrex
    #
    va
    @26
    crab
    #
    @28
    @24
    @32
    va
    @26
    @24
    @30
    vy
    cn0
    wrex
    #
    vx
    cn0
    wrex
    #
    vu
    @23
    wsbc
    @32
    @22
    @35
    vu
    @23
    @22
    @17
    vw
    @20
    wsbc
    vv
    @21
    wsbc
    #
    vx
    cn0
    wrex
    @35
    @17
    @21
    @20
    cn0
    vv
    vw
    vx
    2sbcrex
    @36
    @34
    vx
    cn0
    wph
    @21
    @20
    cn0
    vv
    vw
    vy
    2sbcrex
    rexbii
    bitri
    sbcbii
    @30
    @23
    cn0
    cn0
    vu
    vx
    vy
    sbc2rex
    bitri
    rabbii
    @29
    cL
    cn0
    wcel
    #
    @31
    vy
    @2
    wsbc
    vx
    @4
    wsbc
    #
    va
    @1
    @25
    cres
    #
    wsbc
    #
    vt
    @13
    crab
    #
    @15
    wcel
    #
    @33
    @28
    wcel
    @0
    @37
    @16
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
    @42
    @16
    @0
    @41
    @14
    @15
    @0
    @40
    @12
    vt
    @13
    @40
    @5
    vw
    @20
    wsbc
    #
    vv
    @21
    wsbc
    #
    vu
    @23
    wsbc
    #
    va
    @39
    wsbc
    #
    @0
    @12
    @38
    @49
    va
    @39
    @38
    @30
    vy
    @2
    wsbc
    #
    vx
    @4
    wsbc
    #
    vu
    @23
    wsbc
    @49
    @30
    @23
    @4
    @2
    vu
    vx
    vy
    sbcrot3
    @52
    @48
    vu
    @23
    @52
    @3
    vw
    @20
    wsbc
    vv
    @21
    wsbc
    #
    vx
    @4
    wsbc
    @48
    @51
    @53
    vx
    @4
    wph
    @2
    @21
    @20
    vy
    vv
    vw
    sbcrot3
    sbcbii
    @3
    @4
    @21
    @20
    vx
    vv
    vw
    sbcrot3
    bitri
    sbcbii
    bitr3i
    sbcbii
    @50
    @48
    va
    @39
    wsbc
    #
    vu
    @39
    @10
    cres
    #
    wsbc
    #
    @0
    @12
    @48
    @39
    @23
    @55
    va
    vu
    @19
    @39
    @10
    reseq1
    sbccomieg
    @56
    @54
    vu
    @11
    wsbc
    #
    @0
    @12
    @10
    @25
    wss
    @55
    @11
    wceq
    @56
    @57
    wb
    @10
    c1
    cM
    cfz
    co
    #
    @25
    @10
    c1
    @44
    cfz
    co
    @58
    c1
    cN
    fzssp1
    cM
    @44
    c1
    cfz
    rexfrabdioph.1
    oveq2i
    sseqtr4i
    @58
    c1
    @43
    cfz
    co
    @25
    c1
    cM
    fzssp1
    cL
    @43
    c1
    cfz
    rexfrabdioph.2
    oveq2i
    sseqtr4i
    #
    sstri
    @1
    @10
    @25
    resabs1
    @54
    vu
    @55
    @11
    dfsbcq
    mp2b
    @0
    @54
    @9
    vu
    @11
    @54
    @47
    va
    @39
    wsbc
    #
    vv
    cM
    @39
    cfv
    #
    wsbc
    #
    @0
    @9
    @47
    @39
    @21
    @61
    va
    vv
    cM
    @19
    @39
    fveq1
    sbccomieg
    @0
    @62
    @60
    vv
    @8
    wsbc
    #
    @9
    @0
    cM
    @25
    wcel
    @61
    @8
    wceq
    @62
    @63
    wb
    @0
    @58
    @25
    cM
    @59
    @0
    cM
    cn
    wcel
    cM
    @58
    wcel
    @45
    cM
    elfz1end
    sylib
    sseldi
    cM
    @25
    @1
    fvres
    @60
    vv
    @61
    @8
    dfsbcq
    3syl
    @0
    @60
    @7
    vv
    @8
    @60
    @5
    vw
    cL
    @39
    cfv
    #
    wsbc
    #
    @0
    @7
    @39
    cvv
    wcel
    @60
    @65
    wb
    @1
    @25
    vt
    vex
    resex
    @5
    va
    vw
    @39
    @20
    @64
    cvv
    cL
    @19
    @39
    fveq1
    sbcco3g
    ax-mp
    @0
    cL
    @25
    wcel
    #
    @64
    @6
    wceq
    @65
    @7
    wb
    @0
    cL
    cn
    wcel
    @66
    @46
    cL
    elfz1end
    sylib
    cL
    @25
    @1
    fvres
    @5
    vw
    @64
    @6
    dfsbcq
    3syl
    syl5bb
    sbcbidv
    bitrd
    syl5bb
    sbcbidv
    syl5bb
    syl5bb
    syl5bb
    rabbidv
    eleq1d
    biimpar
    @31
    vy
    vx
    va
    vt
    cJ
    cK
    cL
    rexfrabdioph.3
    rexfrabdioph.4
    2rexfrabdioph
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
