include "wcel.mm"
include "cv.mm"
include "cdia.mm"
include "cfv.mm"
include "cdm.mm"
include "cltrn.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "cdib.mm"
include "dibffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "wceq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "eqidd.mm"
include "mpteq12dv.mm"
include "sneqd.mm"
include "xpeq12d.mm"
include "eqid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "dmex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem dibfval
  let vx: setvar x
  let cB: class B
  let cT: class T
  let vf: setvar f
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  let vw: setvar w
  assume dibval.b: |- B = ( Base ` K )
  assume dibval.h: |- H = ( LHyp ` K )
  assume dibval.t: |- T = ( ( LTrn ` K ) ` W )
  assume dibval.o: |- .0. = ( f e. T |-> ( _I |` B ) )
  assume dibval.j: |- J = ( ( DIsoA ` K ) ` W )
  assume dibval.i: |- I = ( ( DIsoB ` K ) ` W )

  disjoint f x
  disjoint K f
  disjoint K x
  disjoint J x
  disjoint W f
  disjoint W x
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint k x
  disjoint K k
  disjoint w x
  disjoint K w
  disjoint J w
  disjoint .0. w
  disjoint W w
  assert |- ( ( K e. V /\ W e. H ) -> I = ( x e. dom J |-> ( ( J ` x ) X. { .0. } ) ) )

  proof
    cK
    cV
    wcel
    #
    cW
    cH
    wcel
    cI
    cW
    vw
    cH
    vx
    vw
    cv
    #
    cK
    cdia
    cfv
    #
    cfv
    #
    cdm
    #
    vx
    cv
    #
    @3
    cfv
    #
    vf
    @1
    cK
    cltrn
    cfv
    #
    cfv
    #
    cid
    cB
    cres
    #
    cmpt
    #
    csn
    #
    cxp
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    vx
    cJ
    cdm
    #
    @5
    cJ
    cfv
    #
    c.0
    csn
    #
    cxp
    #
    cmpt
    #
    @0
    cI
    cW
    cK
    cdib
    cfv
    #
    cfv
    @15
    dibval.i
    @0
    cW
    @21
    @14
    vx
    vw
    cB
    vf
    cH
    cK
    cV
    dibval.b
    dibval.h
    dibffval
    fveq1d
    syl5eq
    vw
    cW
    @13
    @20
    cH
    @14
    @1
    cW
    wceq
    #
    vx
    @4
    @12
    @16
    @19
    @22
    @3
    cJ
    @22
    @3
    cW
    @2
    cfv
    #
    cJ
    @1
    cW
    @2
    fveq2
    dibval.j
    syl6eqr
    #
    dmeqd
    @22
    @6
    @17
    @11
    @18
    @22
    @5
    @3
    cJ
    @24
    fveq1d
    @22
    @10
    c.0
    @22
    @10
    vf
    cT
    @9
    cmpt
    c.0
    @22
    vf
    @8
    @9
    cT
    @9
    @22
    @8
    cW
    @7
    cfv
    cT
    @1
    cW
    @7
    fveq2
    dibval.t
    syl6eqr
    @22
    @9
    eqidd
    mpteq12dv
    dibval.o
    syl6eqr
    sneqd
    xpeq12d
    mpteq12dv
    @14
    eqid
    vx
    @16
    @19
    cJ
    cJ
    @23
    cvv
    dibval.j
    cW
    @2
    fvex
    eqeltri
    dmex
    mptex
    fvmpt
    sylan9eq
end
