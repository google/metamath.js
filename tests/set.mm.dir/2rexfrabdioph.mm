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
include "rabbii.mm"
include "caddc.mm"
include "peano2nn0.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "sbcrot3.mm"
include "sbcbii.mm"
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
include "cn.mm"
include "nn0p1nn.mm"
include "elfz1end.mm"
include "sylib.mm"
include "fvres.mm"
include "3syl.mm"
include "syl5bb.mm"
include "sbcbidv.mm"
include "syl5rbb.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "biimpa.mm"
include "rexfrabdioph.mm"
include "syl2anc.mm"
include "syldan.mm"

theorem 2rexfrabdioph
  let wph: wff ph
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cL: class L
  let cM: class M
  let cN: class N
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vp: setvar p
  let vq: setvar q
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  assume rexfrabdioph.1: |- M = ( N + 1 )
  assume rexfrabdioph.2: |- L = ( M + 1 )

  disjoint t u
  disjoint t v
  disjoint t w
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint L t
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint M w
  disjoint N t
  disjoint N u
  disjoint N v
  disjoint N w
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
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint p t
  disjoint q t
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint p u
  disjoint q u
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
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint K p
  disjoint K q
  disjoint L a
  disjoint L b
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint L p
  disjoint L q
  disjoint M a
  disjoint M b
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint M p
  disjoint M q
  disjoint N a
  disjoint N b
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N p
  disjoint N q
  disjoint a ph
  disjoint b ph
  assert |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... L ) ) | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. [. ( t ` L ) / w ]. ph } e. ( Dioph ` L ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 E. w e. NN0 ph } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    #
    wph
    vw
    cL
    vt
    cv
    #
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
    cL
    cfz
    co
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
    #
    wph
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
    vu
    @14
    @6
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
    @13
    vv
    cn0
    wrex
    vu
    cn0
    @6
    cmap
    co
    crab
    cN
    cdioph
    cfv
    wcel
    @0
    @12
    wa
    #
    @20
    wph
    vv
    @15
    wsbc
    vu
    @16
    wsbc
    #
    vw
    cn0
    wrex
    #
    va
    @19
    crab
    #
    @21
    @17
    @24
    va
    @19
    wph
    @16
    @15
    cn0
    vu
    vv
    vw
    2sbcrex
    rabbii
    @22
    cM
    cn0
    wcel
    #
    @23
    vw
    @2
    wsbc
    #
    va
    @1
    @18
    cres
    #
    wsbc
    #
    vt
    @9
    crab
    #
    @11
    wcel
    #
    @25
    @21
    wcel
    @0
    @26
    @12
    @0
    cM
    cN
    c1
    caddc
    co
    #
    cn0
    rexfrabdioph.1
    cN
    peano2nn0
    syl5eqel
    adantr
    @0
    @12
    @31
    @0
    @10
    @30
    @11
    @0
    @8
    @29
    vt
    @9
    @29
    @3
    vv
    @15
    wsbc
    #
    vu
    @16
    wsbc
    #
    va
    @28
    wsbc
    #
    @0
    @8
    @27
    @34
    va
    @28
    wph
    @2
    @16
    @15
    vw
    vu
    vv
    sbcrot3
    sbcbii
    @35
    @33
    va
    @28
    wsbc
    #
    vu
    @28
    @6
    cres
    #
    wsbc
    #
    @0
    @8
    @33
    @28
    @16
    @37
    va
    vu
    @14
    @28
    @6
    reseq1
    sbccomieg
    @38
    @36
    vu
    @7
    wsbc
    #
    @0
    @8
    @6
    @18
    wss
    @37
    @7
    wceq
    @38
    @39
    wb
    @6
    c1
    @32
    cfz
    co
    @18
    c1
    cN
    fzssp1
    cM
    @32
    c1
    cfz
    rexfrabdioph.1
    oveq2i
    sseqtr4i
    @1
    @6
    @18
    resabs1
    @36
    vu
    @37
    @7
    dfsbcq
    mp2b
    @0
    @36
    @5
    vu
    @7
    @36
    @3
    vv
    cM
    @28
    cfv
    #
    wsbc
    #
    @0
    @5
    @28
    cvv
    wcel
    @36
    @41
    wb
    @1
    @18
    vt
    vex
    resex
    @3
    va
    vv
    @28
    @15
    @40
    cvv
    cM
    @14
    @28
    fveq1
    sbcco3g
    ax-mp
    @0
    cM
    @18
    wcel
    #
    @40
    @4
    wceq
    @41
    @5
    wb
    @0
    cM
    cn
    wcel
    @42
    @0
    cM
    @32
    cn
    rexfrabdioph.1
    cN
    nn0p1nn
    syl5eqel
    cM
    elfz1end
    sylib
    cM
    @18
    @1
    fvres
    @3
    vv
    @40
    @4
    dfsbcq
    3syl
    syl5bb
    sbcbidv
    syl5bb
    syl5bb
    syl5rbb
    rabbidv
    eleq1d
    biimpa
    @23
    vw
    va
    vt
    cL
    cM
    rexfrabdioph.2
    rexfrabdioph
    syl2anc
    syl5eqel
    @13
    vv
    vu
    va
    cM
    cN
    rexfrabdioph.1
    rexfrabdioph
    syldan
end
