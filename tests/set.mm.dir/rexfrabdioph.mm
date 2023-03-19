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
include "wa.mm"
include "wrex.mm"
include "nfcv.mm"
include "nfv.mm"
include "nfsbc1v.mm"
include "nfrex.mm"
include "wceq.mm"
include "sbceq1a.mm"
include "cbvrex.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "cbvrab.mm"
include "dfsbcq.mm"
include "sbcbidv.mm"
include "rexrabdioph.mm"
include "syl5eqel.mm"

theorem rexfrabdioph
  let wph: wff ph
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cM: class M
  let cN: class N
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vp: setvar p
  let vq: setvar q
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  assume rexfrabdioph.1: |- M = ( N + 1 )

  disjoint t u
  disjoint t v
  disjoint u v
  disjoint M t
  disjoint M u
  disjoint M v
  disjoint N t
  disjoint N u
  disjoint N v
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
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint p t
  disjoint q t
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
  disjoint L t
  disjoint L u
  disjoint L v
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint L p
  disjoint L q
  disjoint M a
  disjoint M b
  disjoint M w
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint M p
  disjoint M q
  disjoint N a
  disjoint N b
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint N p
  disjoint N q
  disjoint a ph
  disjoint b ph
  assert |- ( ( N e. NN0 /\ { t e. ( NN0 ^m ( 1 ... M ) ) | [. ( t |` ( 1 ... N ) ) / u ]. [. ( t ` M ) / v ]. ph } e. ( Dioph ` M ) ) -> { u e. ( NN0 ^m ( 1 ... N ) ) | E. v e. NN0 ph } e. ( Dioph ` N ) )

  proof
    cN
    cn0
    wcel
    wph
    vv
    cM
    vt
    cv
    #
    cfv
    #
    wsbc
    #
    vu
    @0
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
    cM
    cfz
    co
    cmap
    co
    crab
    cM
    cdioph
    cfv
    wcel
    wa
    wph
    vv
    cn0
    wrex
    #
    vu
    cn0
    @3
    cmap
    co
    #
    crab
    wph
    vv
    vb
    cv
    #
    wsbc
    #
    vu
    va
    cv
    #
    wsbc
    #
    vb
    cn0
    wrex
    #
    va
    @7
    crab
    cN
    cdioph
    cfv
    @6
    @12
    vu
    va
    @7
    vu
    @7
    nfcv
    va
    @7
    nfcv
    @6
    va
    nfv
    @11
    vu
    vb
    cn0
    vu
    cn0
    nfcv
    @9
    vu
    @10
    nfsbc1v
    nfrex
    @6
    @9
    vb
    cn0
    wrex
    vu
    cv
    @10
    wceq
    #
    @12
    wph
    @9
    vv
    vb
    cn0
    wph
    vb
    nfv
    wph
    vv
    @8
    nfsbc1v
    wph
    vv
    @8
    sbceq1a
    cbvrex
    @13
    @9
    @11
    vb
    cn0
    @9
    vu
    @10
    sbceq1a
    rexbidv
    syl5bb
    cbvrab
    @5
    @11
    @2
    vu
    @10
    wsbc
    vb
    va
    vt
    cM
    cN
    rexfrabdioph.1
    @8
    @1
    wceq
    @9
    @2
    vu
    @10
    wph
    vv
    @8
    @1
    dfsbcq
    sbcbidv
    @2
    vu
    @10
    @4
    dfsbcq
    rexrabdioph
    syl5eqel
end
