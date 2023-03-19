include "crecs.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wex.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "eldm2g.mm"
include "ibi.mm"
include "wfn.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "dfrecs3.mm"
include "eleq2i.mm"
include "eluniab.mm"
include "bitri.mm"
include "wi.mm"
include "fnop.mm"
include "wss.mm"
include "rspe.mm"
include "abeq2i.mm"
include "elssuni.mm"
include "recsfval.mm"
include "syl6sseqr.mm"
include "sylbir.mm"
include "syl.mm"
include "fveq2.mm"
include "reseq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "fndm.mm"
include "eleq2d.mm"
include "wfun.mm"
include "tfrlem7.mm"
include "funssfv.mm"
include "mp3an1.mm"
include "adantrl.mm"
include "eleq1d.mm"
include "onelss.mm"
include "syl6bir.mm"
include "imp31.mm"
include "w3a.mm"
include "fun2ssres.mm"
include "sylan2.mm"
include "exbiri.mm"
include "com3l.mm"
include "exp31.mm"
include "com34.mm"
include "com24.mm"
include "sylbird.mm"
include "syld.mm"
include "imp4d.mm"
include "mpdi.mm"
include "exp4d.mm"
include "ex.mm"
include "com4r.mm"
include "pm2.43i.mm"
include "imp4a.mm"
include "rexlimdv.mm"
include "imp.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem tfrlem9
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  let vz: setvar z
  let cC: class C
  let va: setvar a
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }

  disjoint f x
  disjoint f y
  disjoint B f
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f h
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g h
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint F g
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint A g
  disjoint A h
  disjoint A z
  assert |- ( B e. dom recs ( F ) -> ( recs ( F ) ` B ) = ( F ` ( recs ( F ) |` B ) ) )

  proof
    cB
    cF
    crecs
    #
    cdm
    #
    wcel
    #
    cB
    vz
    cv
    #
    cop
    #
    @0
    wcel
    #
    vz
    wex
    #
    cB
    @0
    cfv
    #
    @0
    cB
    cres
    #
    cF
    cfv
    #
    wceq
    #
    @2
    @6
    vz
    cB
    @0
    @1
    eldm2g
    ibi
    @5
    @10
    vz
    @5
    @4
    vf
    cv
    #
    wcel
    #
    @11
    vx
    cv
    #
    wfn
    #
    vy
    cv
    #
    @11
    cfv
    #
    @11
    @15
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @13
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    wa
    #
    vf
    wex
    #
    @10
    @5
    @4
    @22
    vf
    cab
    cuni
    #
    wcel
    @24
    @0
    @25
    @4
    vx
    vy
    vf
    cF
    dfrecs3
    eleq2i
    @22
    vf
    @4
    eluniab
    bitri
    @23
    @10
    vf
    @12
    @22
    @10
    @12
    @21
    @10
    vx
    con0
    @12
    @13
    con0
    wcel
    #
    @14
    @20
    @10
    @14
    @12
    @26
    @20
    @10
    wi
    #
    @14
    @12
    @26
    @27
    wi
    wi
    @14
    @12
    @26
    @14
    @27
    @14
    @12
    @26
    @14
    @27
    wi
    wi
    @14
    @12
    wa
    #
    @26
    @14
    @20
    @10
    @28
    cB
    @13
    wcel
    #
    @26
    @21
    wa
    #
    @10
    wi
    @13
    cB
    @3
    @11
    fnop
    @29
    @30
    @11
    @0
    wss
    #
    @10
    @30
    @22
    @31
    @21
    vx
    con0
    rspe
    @22
    @11
    cA
    wcel
    #
    @31
    @22
    vf
    cA
    tfrlem.1
    abeq2i
    @32
    @11
    cA
    cuni
    @0
    @11
    cA
    elssuni
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    recsfval
    syl6sseqr
    sylbir
    syl
    @29
    @26
    @14
    @20
    @31
    @10
    wi
    #
    @29
    @20
    @14
    @26
    @33
    @29
    @20
    cB
    @11
    cfv
    #
    @11
    cB
    cres
    #
    cF
    cfv
    #
    wceq
    #
    @14
    @26
    @33
    wi
    #
    wi
    @19
    @37
    vy
    cB
    @13
    @15
    cB
    wceq
    #
    @16
    @34
    @18
    @36
    @15
    cB
    @11
    fveq2
    @39
    @17
    @35
    cF
    @15
    cB
    @11
    reseq2
    fveq2d
    eqeq12d
    rspcv
    @14
    @29
    @37
    @38
    @14
    @29
    cB
    @11
    cdm
    #
    wcel
    #
    @37
    @38
    wi
    @14
    @40
    @13
    cB
    @13
    @11
    fndm
    #
    eleq2d
    @14
    @26
    @37
    @41
    @33
    @14
    @26
    @41
    @37
    @33
    @14
    @26
    @41
    @37
    @33
    wi
    @31
    @14
    @26
    wa
    #
    @41
    wa
    #
    @37
    @10
    @31
    @44
    @10
    @37
    @31
    @44
    wa
    @7
    @34
    @9
    @36
    @31
    @41
    @7
    @34
    wceq
    #
    @43
    @0
    wfun
    #
    @31
    @41
    @45
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem7
    #
    cB
    @0
    @11
    funssfv
    mp3an1
    adantrl
    @44
    @31
    cB
    @40
    wss
    #
    @9
    @36
    wceq
    #
    @14
    @26
    @41
    @48
    @14
    @26
    @40
    con0
    wcel
    @41
    @48
    wi
    @14
    @40
    @13
    con0
    @42
    eleq1d
    @40
    cB
    onelss
    syl6bir
    imp31
    @46
    @31
    @48
    @49
    @47
    @46
    @31
    @48
    w3a
    @8
    @35
    cF
    cB
    @0
    @11
    fun2ssres
    fveq2d
    mp3an1
    sylan2
    eqeq12d
    exbiri
    com3l
    exp31
    com34
    com24
    sylbird
    com3l
    syld
    com24
    imp4d
    mpdi
    syl
    exp4d
    ex
    com4r
    pm2.43i
    com3l
    imp4a
    rexlimdv
    imp
    exlimiv
    sylbi
    exlimiv
    syl
end
