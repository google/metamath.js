include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "csn.mm"
include "ctc.mm"
include "cfv.mm"
include "wral.mm"
include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "crab.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "eleq1d.mm"
include "cmpt.mm"
include "crdg.mm"
include "com.mm"
include "cres.mm"
include "cxp.mm"
include "cpw.mm"
include "char.mm"
include "crnk.mm"
include "cep.mm"
include "coi.mm"
include "vex.mm"
include "eqid.mm"
include "rdgeq2.mm"
include "unieq.mm"
include "cbvmptv.mm"
include "rdgeq1.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "reseq1d.mm"
include "hsmexlem6.mm"
include "vtoclg.mm"

theorem hsmex
  let vx: setvar x
  let cV: class V
  let cX: class X
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vy: setvar y
  let vz: setvar z

  disjoint s x
  disjoint X s
  disjoint X x
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a s
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint X a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b s
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint X b
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c s
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint X c
  disjoint d e
  disjoint d f
  disjoint d s
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint X d
  disjoint e f
  disjoint e s
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint X e
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint X f
  disjoint s y
  disjoint s z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint X y
  disjoint X z
  assert |- ( X e. V -> { s e. U. ( R1 " On ) | A. x e. ( TC ` { s } ) x ~<_ X } e. _V )

  proof
    vx
    cv
    #
    va
    cv
    #
    cdom
    wbr
    #
    vx
    vs
    cv
    csn
    ctc
    cfv
    #
    wral
    #
    vs
    cr1
    con0
    cima
    cuni
    #
    crab
    #
    cvv
    wcel
    @0
    cX
    cdom
    wbr
    #
    vx
    @3
    wral
    #
    vs
    @5
    crab
    #
    cvv
    wcel
    va
    cX
    cV
    @1
    cX
    wceq
    #
    @6
    @9
    cvv
    @10
    @4
    @8
    vs
    @5
    @10
    @2
    @7
    vx
    @3
    @1
    cX
    @0
    cdom
    breq2
    ralbidv
    rabbidv
    eleq1d
    vb
    vc
    vd
    @6
    ve
    cvv
    vf
    cvv
    vf
    cv
    #
    cuni
    #
    cmpt
    #
    ve
    cv
    #
    crdg
    #
    com
    cres
    #
    cmpt
    #
    vd
    cvv
    @1
    vd
    cv
    cxp
    cpw
    char
    cfv
    cmpt
    @1
    cpw
    char
    cfv
    crdg
    com
    cres
    #
    crnk
    vy
    cv
    vz
    cv
    @17
    cfv
    cfv
    cima
    cep
    coi
    #
    @1
    vs
    vx
    vy
    vz
    va
    vex
    @18
    eqid
    ve
    vb
    cvv
    @16
    vc
    cvv
    vc
    cv
    #
    cuni
    #
    cmpt
    #
    vb
    cv
    #
    crdg
    #
    com
    cres
    @14
    @23
    wceq
    #
    @15
    @24
    com
    @25
    @15
    @13
    @23
    crdg
    #
    @24
    @14
    @23
    @13
    rdgeq2
    @13
    @22
    wceq
    @26
    @24
    wceq
    vf
    vc
    cvv
    @12
    @21
    @11
    @20
    unieq
    cbvmptv
    @23
    @13
    @22
    rdgeq1
    ax-mp
    syl6eq
    reseq1d
    cbvmptv
    @6
    eqid
    @19
    eqid
    hsmexlem6
    vtoclg
end
