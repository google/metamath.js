include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cdia.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "dibval2.mm"
include "eleq2d.mm"
include "wex.mm"
include "diaelval.mm"
include "anbi1d.mm"
include "an13.mm"
include "velsn.mm"
include "anbi1i.mm"
include "bitri.mm"
include "exbii.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "cvv.mm"
include "cltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "opeq2.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "ceqsexv.mm"
include "anass.mm"
include "an32.mm"
include "bitr3i.mm"
include "3bitr4g.mm"
include "exbidv.mm"
include "elxp.mm"
include "df-rex.mm"
include "bitrd.mm"

theorem dibelval3
  let cB: class B
  let cR: class R
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vs: setvar s
  assume dibval3.b: |- B = ( Base ` K )
  assume dibval3.l: |- .<_ = ( le ` K )
  assume dibval3.h: |- H = ( LHyp ` K )
  assume dibval3.t: |- T = ( ( LTrn ` K ) ` W )
  assume dibval3.r: |- R = ( ( trL ` K ) ` W )
  assume dibval3.o: |- .0. = ( g e. T |-> ( _I |` B ) )
  assume dibval3.i: |- I = ( ( DIsoB ` K ) ` W )

  disjoint K f
  disjoint K g
  disjoint T f
  disjoint W f
  disjoint W g
  disjoint X f
  disjoint .<_ f
  disjoint B f
  disjoint H f
  disjoint .0. f
  disjoint T g
  disjoint V f
  disjoint Y f
  disjoint K s
  disjoint f s
  disjoint .0. s
  disjoint W s
  disjoint X s
  disjoint Y s
  assert |- ( ( ( K e. V /\ W e. H ) /\ ( X e. B /\ X .<_ W ) ) -> ( Y e. ( I ` X ) <-> E. f e. T ( Y = <. f , .0. >. /\ ( R ` f ) .<_ X ) ) )

  proof
    cK
    cV
    wcel
    cW
    cH
    wcel
    wa
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wa
    wa
    #
    cY
    cX
    cI
    cfv
    #
    wcel
    cY
    cX
    cW
    cK
    cdia
    cfv
    cfv
    #
    cfv
    #
    c.0
    csn
    #
    cxp
    #
    wcel
    #
    cY
    vf
    cv
    #
    c.0
    cop
    #
    wceq
    #
    @7
    cR
    cfv
    cX
    c.le
    wbr
    #
    wa
    #
    vf
    cT
    wrex
    #
    @0
    @1
    @5
    cY
    cB
    cT
    vg
    cH
    cI
    @2
    cK
    c.le
    cV
    cW
    cX
    c.0
    dibval3.b
    dibval3.l
    dibval3.h
    dibval3.t
    dibval3.o
    @2
    eqid
    #
    dibval3.i
    dibval2
    eleq2d
    @0
    cY
    @7
    vs
    cv
    #
    cop
    #
    wceq
    #
    @7
    @3
    wcel
    #
    @14
    @4
    wcel
    #
    wa
    wa
    #
    vs
    wex
    #
    vf
    wex
    @7
    cT
    wcel
    #
    @11
    wa
    #
    vf
    wex
    @6
    @12
    @0
    @20
    @22
    vf
    @0
    @17
    @9
    wa
    #
    @21
    @10
    wa
    #
    @9
    wa
    #
    @20
    @22
    @0
    @17
    @24
    @9
    cB
    cR
    cT
    @7
    cH
    @2
    cK
    c.le
    cV
    cW
    cX
    dibval3.b
    dibval3.l
    dibval3.h
    dibval3.t
    dibval3.r
    @13
    diaelval
    anbi1d
    @20
    @14
    c.0
    wceq
    #
    @17
    @16
    wa
    #
    wa
    #
    vs
    wex
    @23
    @19
    @28
    vs
    @19
    @18
    @27
    wa
    @28
    @16
    @17
    @18
    an13
    @18
    @26
    @27
    vs
    c.0
    velsn
    anbi1i
    bitri
    exbii
    @27
    @23
    vs
    c.0
    c.0
    vg
    cT
    cid
    cB
    cres
    #
    cmpt
    cvv
    dibval3.o
    vg
    cT
    @29
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    cvv
    dibval3.t
    cW
    @30
    fvex
    eqeltri
    mptex
    eqeltri
    @26
    @16
    @9
    @17
    @26
    @15
    @8
    cY
    @14
    c.0
    @7
    opeq2
    eqeq2d
    anbi2d
    ceqsexv
    bitri
    @22
    @21
    @9
    wa
    @10
    wa
    @25
    @21
    @9
    @10
    anass
    @21
    @9
    @10
    an32
    bitr3i
    3bitr4g
    exbidv
    vf
    vs
    cY
    @3
    @4
    elxp
    @11
    vf
    cT
    df-rex
    3bitr4g
    bitrd
end
