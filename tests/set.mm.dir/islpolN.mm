include "wcel.mm"
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
include "wf.mm"
include "lpolsetN.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "sseq12d.mm"
include "imbi2d.mm"
include "2albidv.mm"
include "eleq1d.mm"
include "id.mm"
include "fveq12d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "elrab.mm"
include "clss.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cbs.mm"
include "pwex.mm"
include "elmap.mm"
include "anbi1i.mm"
include "bitri.mm"
include "syl6bb.mm"

theorem islpolN
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cS: class S
  let cH: class H
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vo: setvar o
  assume lpolset.v: |- V = ( Base ` W )
  assume lpolset.s: |- S = ( LSubSp ` W )
  assume lpolset.z: |- .0. = ( 0g ` W )
  assume lpolset.a: |- A = ( LSAtoms ` W )
  assume lpolset.h: |- H = ( LSHyp ` W )
  assume lpolset.p: |- P = ( LPol ` W )

  disjoint A x
  disjoint x y
  disjoint W x
  disjoint W y
  disjoint ._|_ x
  disjoint ._|_ y
  disjoint w x
  disjoint A w
  disjoint H w
  disjoint o w
  disjoint S o
  disjoint S w
  disjoint V o
  disjoint V w
  disjoint o x
  disjoint o y
  disjoint W o
  disjoint w y
  disjoint W w
  disjoint .0. w
  disjoint A o
  disjoint H o
  disjoint ._|_ o
  disjoint .0. o
  assert |- ( W e. X -> ( ._|_ e. P <-> ( ._|_ : ~P V --> S /\ ( ( ._|_ ` V ) = { .0. } /\ A. x A. y ( ( x C_ V /\ y C_ V /\ x C_ y ) -> ( ._|_ ` y ) C_ ( ._|_ ` x ) ) /\ A. x e. A ( ( ._|_ ` x ) e. H /\ ( ._|_ ` ( ._|_ ` x ) ) = x ) ) ) ) )

  proof
    cW
    cX
    wcel
    #
    c.pe
    cP
    wcel
    c.pe
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
    vy
    cv
    #
    cV
    wss
    @5
    @6
    wss
    w3a
    #
    @6
    @1
    cfv
    #
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
    @9
    cH
    wcel
    #
    @9
    @1
    cfv
    #
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
    wcel
    #
    @19
    cS
    c.pe
    wf
    #
    cV
    c.pe
    cfv
    #
    @3
    wceq
    #
    @7
    @6
    c.pe
    cfv
    #
    @5
    c.pe
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
    @27
    cH
    wcel
    #
    @27
    c.pe
    cfv
    #
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
    wa
    #
    @0
    cP
    @21
    c.pe
    vx
    vy
    cA
    cP
    cS
    vo
    cH
    cV
    cW
    cX
    c.0
    lpolset.v
    lpolset.s
    lpolset.z
    lpolset.a
    lpolset.h
    lpolset.p
    lpolsetN
    eleq2d
    @22
    c.pe
    @20
    wcel
    #
    @36
    wa
    @37
    @18
    @36
    vo
    c.pe
    @20
    @1
    c.pe
    wceq
    #
    @4
    @25
    @12
    @30
    @17
    @35
    @39
    @2
    @24
    @3
    cV
    @1
    c.pe
    fveq1
    eqeq1d
    @39
    @11
    @29
    vx
    vy
    @39
    @10
    @28
    @7
    @39
    @8
    @26
    @9
    @27
    @6
    @1
    c.pe
    fveq1
    @5
    @1
    c.pe
    fveq1
    #
    sseq12d
    imbi2d
    2albidv
    @39
    @16
    @34
    vx
    cA
    @39
    @13
    @31
    @15
    @33
    @39
    @9
    @27
    cH
    @40
    eleq1d
    @39
    @14
    @32
    @5
    @39
    @9
    @27
    @1
    c.pe
    @39
    id
    @40
    fveq12d
    eqeq1d
    anbi12d
    ralbidv
    3anbi123d
    elrab
    @38
    @23
    @36
    cS
    @19
    c.pe
    cS
    cW
    clss
    cfv
    cvv
    lpolset.s
    cW
    clss
    fvex
    eqeltri
    cV
    cV
    cW
    cbs
    cfv
    cvv
    lpolset.v
    cW
    cbs
    fvex
    eqeltri
    pwex
    elmap
    anbi1i
    bitri
    syl6bb
end
