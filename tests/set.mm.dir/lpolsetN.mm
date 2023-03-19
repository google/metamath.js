include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "wss.mm"
include "w3a.mm"
include "wi.mm"
include "wal.mm"
include "wa.mm"
include "wral.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "crab.mm"
include "elex.mm"
include "clpoN.mm"
include "cbs.mm"
include "c0g.mm"
include "clsh.mm"
include "clsa.mm"
include "clss.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "eqeq12d.mm"
include "sseq2d.mm"
include "3anbi12d.mm"
include "imbi1d.mm"
include "2albidv.mm"
include "eleq2d.mm"
include "anbi1d.mm"
include "raleqbidv.mm"
include "3anbi123d.mm"
include "rabeqbidv.mm"
include "df-lpolN.mm"
include "ovex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem lpolsetN
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cS: class S
  let vo: setvar o
  let cH: class H
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  assume lpolset.v: |- V = ( Base ` W )
  assume lpolset.s: |- S = ( LSubSp ` W )
  assume lpolset.z: |- .0. = ( 0g ` W )
  assume lpolset.a: |- A = ( LSAtoms ` W )
  assume lpolset.h: |- H = ( LSHyp ` W )
  assume lpolset.p: |- P = ( LPol ` W )

  disjoint A x
  disjoint S o
  disjoint V o
  disjoint o x
  disjoint o y
  disjoint W o
  disjoint x y
  disjoint W x
  disjoint W y
  disjoint w x
  disjoint A w
  disjoint H w
  disjoint o w
  disjoint S w
  disjoint V w
  disjoint w y
  disjoint W w
  disjoint .0. w
  assert |- ( W e. X -> P = { o e. ( S ^m ~P V ) | ( ( o ` V ) = { .0. } /\ A. x A. y ( ( x C_ V /\ y C_ V /\ x C_ y ) -> ( o ` y ) C_ ( o ` x ) ) /\ A. x e. A ( ( o ` x ) e. H /\ ( o ` ( o ` x ) ) = x ) ) } )

  proof
    cW
    cX
    wcel
    cW
    cvv
    wcel
    #
    cP
    cV
    vo
    cv
    #
    cfv
    #
    c.0
    csn
    #
    wceq
    #
    vx
    cv
    #
    cV
    wss
    #
    vy
    cv
    #
    cV
    wss
    #
    @5
    @7
    wss
    #
    w3a
    #
    @7
    @1
    cfv
    @5
    @1
    cfv
    #
    wss
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @11
    cH
    wcel
    #
    @11
    @1
    cfv
    @5
    wceq
    #
    wa
    #
    vx
    cA
    wral
    #
    w3a
    #
    vo
    cS
    cV
    cpw
    #
    cmap
    co
    #
    crab
    #
    wceq
    cW
    cX
    elex
    @0
    cP
    cW
    clpoN
    cfv
    @22
    lpolset.p
    vw
    cW
    vw
    cv
    #
    cbs
    cfv
    #
    @1
    cfv
    #
    @23
    c0g
    cfv
    #
    csn
    #
    wceq
    #
    @5
    @24
    wss
    #
    @7
    @24
    wss
    #
    @9
    w3a
    #
    @12
    wi
    #
    vy
    wal
    vx
    wal
    #
    @11
    @23
    clsh
    cfv
    #
    wcel
    #
    @16
    wa
    #
    vx
    @23
    clsa
    cfv
    #
    wral
    #
    w3a
    #
    vo
    @23
    clss
    cfv
    #
    @24
    cpw
    #
    cmap
    co
    #
    crab
    @22
    cvv
    clpoN
    @23
    cW
    wceq
    #
    @39
    @19
    vo
    @42
    @21
    @43
    @40
    cS
    @41
    @20
    cmap
    @43
    @40
    cW
    clss
    cfv
    cS
    @23
    cW
    clss
    fveq2
    lpolset.s
    syl6eqr
    @43
    @24
    cV
    @43
    @24
    cW
    cbs
    cfv
    cV
    @23
    cW
    cbs
    fveq2
    lpolset.v
    syl6eqr
    #
    pweqd
    oveq12d
    @43
    @28
    @4
    @33
    @14
    @38
    @18
    @43
    @25
    @2
    @27
    @3
    @43
    @24
    cV
    @1
    @44
    fveq2d
    @43
    @26
    c.0
    @43
    @26
    cW
    c0g
    cfv
    c.0
    @23
    cW
    c0g
    fveq2
    lpolset.z
    syl6eqr
    sneqd
    eqeq12d
    @43
    @32
    @13
    vx
    vy
    @43
    @31
    @10
    @12
    @43
    @29
    @6
    @30
    @8
    @9
    @43
    @24
    cV
    @5
    @44
    sseq2d
    @43
    @24
    cV
    @7
    @44
    sseq2d
    3anbi12d
    imbi1d
    2albidv
    @43
    @36
    @17
    vx
    @37
    cA
    @43
    @37
    cW
    clsa
    cfv
    cA
    @23
    cW
    clsa
    fveq2
    lpolset.a
    syl6eqr
    @43
    @35
    @15
    @16
    @43
    @34
    cH
    @11
    @43
    @34
    cW
    clsh
    cfv
    cH
    @23
    cW
    clsh
    fveq2
    lpolset.h
    syl6eqr
    eleq2d
    anbi1d
    raleqbidv
    3anbi123d
    rabeqbidv
    vx
    vy
    vw
    vo
    df-lpolN
    @19
    vo
    @21
    cS
    @20
    cmap
    ovex
    rabex
    fvmpt
    syl5eq
    syl
end
