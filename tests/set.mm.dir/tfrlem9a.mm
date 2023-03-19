include "crecs.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cop.mm"
include "cv.mm"
include "wa.mm"
include "cres.mm"
include "cvv.mm"
include "wex.mm"
include "wfun.mm"
include "tfrlem7.mm"
include "funfvop.mm"
include "mpan.mm"
include "cuni.mm"
include "recsfval.mm"
include "eleq2i.mm"
include "eluni.mm"
include "bitri.mm"
include "sylib.mm"
include "wfn.mm"
include "wceq.mm"
include "wral.mm"
include "con0.mm"
include "wrex.mm"
include "simprr.mm"
include "vex.mm"
include "tfrlem3a.mm"
include "wss.mm"
include "a1i.mm"
include "simplrr.mm"
include "elssuni.mm"
include "syl.mm"
include "syl6sseqr.mm"
include "word.mm"
include "fndm.mm"
include "ad2antll.mm"
include "simprl.mm"
include "eqeltrd.mm"
include "eloni.mm"
include "wbr.mm"
include "simpll.mm"
include "fvexd.mm"
include "simplrl.mm"
include "df-br.mm"
include "sylibr.mm"
include "breldmg.mm"
include "syl3anc.mm"
include "ordelss.mm"
include "syl2anc.mm"
include "fun2ssres.mm"
include "resex.mm"
include "expr.mm"
include "adantrd.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "exlimddv.mm"

theorem tfrlem9a
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
  assert |- ( B e. dom recs ( F ) -> ( recs ( F ) |` B ) e. _V )

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
    cB
    @0
    cfv
    #
    cop
    #
    vg
    cv
    #
    wcel
    #
    @5
    cA
    wcel
    #
    wa
    #
    @0
    cB
    cres
    #
    cvv
    wcel
    #
    vg
    @2
    @4
    @0
    wcel
    #
    @8
    vg
    wex
    #
    @0
    wfun
    #
    @2
    @11
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
    funfvop
    mpan
    @11
    @4
    cA
    cuni
    #
    wcel
    @12
    @0
    @15
    @4
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    recsfval
    #
    eleq2i
    vg
    @4
    cA
    eluni
    bitri
    sylib
    @2
    @8
    wa
    #
    @5
    vz
    cv
    #
    wfn
    #
    va
    cv
    #
    @5
    cfv
    @5
    @20
    cres
    cF
    cfv
    wceq
    va
    @18
    wral
    #
    wa
    #
    vz
    con0
    wrex
    #
    @10
    @17
    @7
    @23
    @2
    @6
    @7
    simprr
    vx
    vy
    vz
    va
    cA
    vf
    cF
    @5
    tfrlem.1
    vg
    vex
    #
    tfrlem3a
    sylib
    @17
    @22
    @10
    vz
    con0
    @17
    @18
    con0
    wcel
    #
    wa
    @19
    @10
    @21
    @17
    @25
    @19
    @10
    @17
    @25
    @19
    wa
    #
    wa
    #
    @9
    @5
    cB
    cres
    #
    cvv
    @27
    @13
    @5
    @0
    wss
    cB
    @5
    cdm
    #
    wss
    #
    @9
    @28
    wceq
    @13
    @27
    @14
    a1i
    @27
    @5
    @15
    @0
    @27
    @7
    @5
    @15
    wss
    @2
    @6
    @7
    @26
    simplrr
    @5
    cA
    elssuni
    syl
    @16
    syl6sseqr
    @27
    @29
    word
    #
    cB
    @29
    wcel
    #
    @30
    @27
    @29
    con0
    wcel
    @31
    @27
    @29
    @18
    con0
    @19
    @29
    @18
    wceq
    @17
    @25
    @18
    @5
    fndm
    ad2antll
    @17
    @25
    @19
    simprl
    eqeltrd
    @29
    eloni
    syl
    @27
    @2
    @3
    cvv
    wcel
    cB
    @3
    @5
    wbr
    #
    @32
    @2
    @8
    @26
    simpll
    @27
    cB
    @0
    fvexd
    @27
    @6
    @33
    @2
    @6
    @7
    @26
    simplrl
    cB
    @3
    @5
    df-br
    sylibr
    cB
    @3
    @1
    cvv
    @5
    breldmg
    syl3anc
    @29
    cB
    ordelss
    syl2anc
    cB
    @0
    @5
    fun2ssres
    syl3anc
    @28
    cvv
    wcel
    @27
    @5
    cB
    @24
    resex
    a1i
    eqeltrd
    expr
    adantrd
    rexlimdva
    mpd
    exlimddv
end
