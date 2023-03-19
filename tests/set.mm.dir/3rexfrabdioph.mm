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
include "sbcbii.mm"
include "bitri.mm"
include "rabbii.mm"
include "caddc.mm"
include "cn.mm"
include "nn0p1nn.mm"
include "syl5eqel.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "sbcrot3.mm"
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
include "2rexfrabdioph.mm"
include "syl2anc.mm"
include "rexfrabdioph.mm"
include "syldan.mm"

theorem 3rexfrabdioph
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vz: setvar z
  let vp: setvar p
  let vq: setvar q
  let cH: class H
  let cI: class I
  let cJ: class J
  assume rexfrabdioph.1: |- M = ( N + 1 )
  assume rexfrabdioph.2: |- L = ( M + 1 )
  assume rexfrabdioph.3: |- K = ( L + 1 )

  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint L t
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint M x
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint N w
  disjoint N x
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
  disjoint t y
  disjoint t z
  disjoint p t
  disjoint q t
  disjoint u y
  disjoint u z
  disjoint p u
  disjoint q u
  disjoint v y
  disjoint v z
  disjoint p v
  disjoint q v
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
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint J p
  disjoint J q
  disjoint K a
  disjoint K b
  disjoint K y
  disjoint K z
  disjoint K p
  disjoint K q
  disjoint L a
  disjoint L b
  disjoint L y
  disjoint L z
  disjoint L p
  disjoint L q
  disjoint M a
  disjoint M b
  disjoint M y
  disjoint M z
  disjoint M p
  disjoint M q
  disjoint N a
  disjoint N b
  disjoint N y
  disjoint N z
  disjoint N p
  disjoint N q
  disjoint a ph
  disjoint b ph
  assert |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... K ) ) | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. [. ( t ` L ) / w ]. [. ( t ` K ) / x ]. ph } e. ( Dioph ` K ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 E. x e. NN0 ph } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    wph
    vx
    cK
    vt
    cv
    #
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
    cK
    cfz
    co
    cmap
    co
    #
    crab
    #
    cK
    cdioph
    cfv
    #
    wcel
    #
    wph
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
    @15
    @7
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
    @14
    vv
    cn0
    wrex
    vu
    cn0
    @7
    cmap
    co
    crab
    cN
    cdioph
    cfv
    wcel
    @0
    @13
    wa
    #
    @22
    wph
    vv
    @16
    wsbc
    #
    vu
    @18
    wsbc
    #
    vx
    cn0
    wrex
    vw
    cn0
    wrex
    #
    va
    @21
    crab
    #
    @23
    @19
    @27
    va
    @21
    @19
    @25
    vx
    cn0
    wrex
    vw
    cn0
    wrex
    #
    vu
    @18
    wsbc
    @27
    @17
    @29
    vu
    @18
    wph
    @16
    cn0
    cn0
    vv
    vw
    vx
    sbc2rex
    sbcbii
    @25
    @18
    cn0
    cn0
    vu
    vw
    vx
    sbc2rex
    bitri
    rabbii
    @24
    cM
    cn0
    wcel
    #
    @26
    vx
    @2
    wsbc
    vw
    @3
    wsbc
    #
    va
    @1
    @20
    cres
    #
    wsbc
    #
    vt
    @10
    crab
    #
    @12
    wcel
    #
    @28
    @23
    wcel
    @0
    @30
    @13
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
    @35
    @13
    @0
    @34
    @11
    @12
    @0
    @33
    @9
    vt
    @10
    @33
    @4
    vv
    @16
    wsbc
    #
    vu
    @18
    wsbc
    #
    va
    @32
    wsbc
    #
    @0
    @9
    @39
    @31
    va
    @32
    @39
    @25
    vx
    @2
    wsbc
    vw
    @3
    wsbc
    #
    vu
    @18
    wsbc
    @31
    @38
    @41
    vu
    @18
    wph
    @16
    @3
    @2
    vv
    vw
    vx
    sbcrot3
    sbcbii
    @25
    @18
    @3
    @2
    vu
    vw
    vx
    sbcrot3
    bitri
    sbcbii
    @40
    @38
    va
    @32
    wsbc
    #
    vu
    @32
    @7
    cres
    #
    wsbc
    #
    @0
    @9
    @38
    @32
    @18
    @43
    va
    vu
    @15
    @32
    @7
    reseq1
    sbccomieg
    @44
    @42
    vu
    @8
    wsbc
    #
    @0
    @9
    @7
    @20
    wss
    @43
    @8
    wceq
    @44
    @45
    wb
    @7
    c1
    @36
    cfz
    co
    @20
    c1
    cN
    fzssp1
    cM
    @36
    c1
    cfz
    rexfrabdioph.1
    oveq2i
    sseqtr4i
    @1
    @7
    @20
    resabs1
    @42
    vu
    @43
    @8
    dfsbcq
    mp2b
    @0
    @42
    @6
    vu
    @8
    @42
    @4
    vv
    cM
    @32
    cfv
    #
    wsbc
    #
    @0
    @6
    @32
    cvv
    wcel
    @42
    @47
    wb
    @1
    @20
    vt
    vex
    resex
    @4
    va
    vv
    @32
    @16
    @46
    cvv
    cM
    @15
    @32
    fveq1
    sbcco3g
    ax-mp
    @0
    cM
    @20
    wcel
    #
    @46
    @5
    wceq
    @47
    @6
    wb
    @0
    cM
    cn
    wcel
    @48
    @37
    cM
    elfz1end
    sylib
    cM
    @20
    @1
    fvres
    @4
    vv
    @46
    @5
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
    @26
    vx
    vw
    va
    vt
    cK
    cL
    cM
    rexfrabdioph.2
    rexfrabdioph.3
    2rexfrabdioph
    syl2anc
    syl5eqel
    @14
    vv
    vu
    va
    cM
    cN
    rexfrabdioph.1
    rexfrabdioph
    syldan
end
