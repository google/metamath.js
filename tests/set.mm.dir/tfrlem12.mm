include "crecs.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "cdm.mm"
include "word.mm"
include "tfrlem8.mm"
include "a1i.mm"
include "dmexg.mm"
include "elon2.mm"
include "sylanbrc.mm"
include "csuc.mm"
include "suceloni.mm"
include "tfrlem10.mm"
include "tfrlem11.mm"
include "ralrimiv.mm"
include "fveq2.mm"
include "reseq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "fneq2.mm"
include "raleq.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "syl.mm"
include "wb.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "snex.mm"
include "unexg.mm"
include "mpan2.mm"
include "syl5eqel.mm"
include "fneq1.mm"
include "fveq1.mm"
include "reseq1.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "elab2g.mm"
include "mpbird.mm"

theorem tfrlem12
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cC: class C
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  let vz: setvar z
  let cB: class B
  let va: setvar a
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }
  assume tfrlem.3: |- C = ( recs ( F ) u. { <. dom recs ( F ) , ( F ` recs ( F ) ) >. } )

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f z
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
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
  assert |- ( recs ( F ) e. _V -> C e. A )

  proof
    cF
    crecs
    #
    cvv
    wcel
    #
    cC
    cA
    wcel
    #
    cC
    vx
    cv
    #
    wfn
    #
    vy
    cv
    #
    cC
    cfv
    #
    cC
    @5
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @3
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    @1
    @0
    cdm
    #
    con0
    wcel
    #
    @12
    @1
    @13
    word
    #
    @13
    cvv
    wcel
    @14
    @15
    @1
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    tfrlem8
    a1i
    @0
    cvv
    dmexg
    @13
    elon2
    sylanbrc
    @14
    @13
    csuc
    #
    con0
    wcel
    cC
    @16
    wfn
    #
    @9
    vy
    @16
    wral
    #
    @12
    @13
    suceloni
    vx
    vy
    cA
    cC
    vf
    cF
    tfrlem.1
    tfrlem.3
    tfrlem10
    @14
    vz
    cv
    #
    cC
    cfv
    #
    cC
    @19
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vz
    @16
    wral
    @18
    @14
    @23
    vz
    @16
    vx
    vy
    cA
    @19
    cC
    vf
    cF
    tfrlem.1
    tfrlem.3
    tfrlem11
    ralrimiv
    @23
    @9
    vz
    vy
    @16
    @19
    @5
    wceq
    #
    @20
    @6
    @22
    @8
    @19
    @5
    cC
    fveq2
    @24
    @21
    @7
    cF
    @19
    @5
    cC
    reseq2
    fveq2d
    eqeq12d
    cbvralv
    sylib
    @11
    @17
    @18
    wa
    vx
    @16
    con0
    @3
    @16
    wceq
    @4
    @17
    @10
    @18
    @3
    @16
    cC
    fneq2
    @9
    vy
    @3
    @16
    raleq
    anbi12d
    rspcev
    syl12anc
    syl
    @1
    cC
    cvv
    wcel
    @2
    @12
    wb
    @1
    cC
    @0
    @13
    @0
    cF
    cfv
    cop
    #
    csn
    #
    cun
    #
    cvv
    tfrlem.3
    @1
    @26
    cvv
    wcel
    @27
    cvv
    wcel
    @25
    snex
    @0
    @26
    cvv
    cvv
    unexg
    mpan2
    syl5eqel
    vf
    cv
    #
    @3
    wfn
    #
    @5
    @28
    cfv
    #
    @28
    @5
    cres
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @3
    wral
    #
    wa
    #
    vx
    con0
    wrex
    @12
    vf
    cC
    cA
    cvv
    @28
    cC
    wceq
    #
    @35
    @11
    vx
    con0
    @36
    @29
    @4
    @34
    @10
    @3
    @28
    cC
    fneq1
    @36
    @33
    @9
    vy
    @3
    @36
    @30
    @6
    @32
    @8
    @5
    @28
    cC
    fveq1
    @36
    @31
    @7
    cF
    @28
    cC
    @5
    reseq1
    fveq2d
    eqeq12d
    ralbidv
    anbi12d
    rexbidv
    tfrlem.1
    elab2g
    syl
    mpbird
end
