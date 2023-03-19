include "wcel.mm"
include "cvv.mm"
include "cdib.mm"
include "cfv.mm"
include "cv.mm"
include "cdia.mm"
include "cdm.mm"
include "cltrn.mm"
include "cid.mm"
include "cres.mm"
include "cmpt.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "dmeqd.mm"
include "reseq2d.mm"
include "mpteq12dv.mm"
include "sneqd.mm"
include "xpeq12d.mm"
include "df-dib.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem dibffval
  let vx: setvar x
  let vw: setvar w
  let cB: class B
  let vf: setvar f
  let cH: class H
  let cK: class K
  let cV: class V
  let vk: setvar k
  assume dibval.b: |- B = ( Base ` K )
  assume dibval.h: |- H = ( LHyp ` K )

  disjoint H w
  disjoint f w
  disjoint f x
  disjoint K f
  disjoint w x
  disjoint K w
  disjoint K x
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint f k
  disjoint k x
  disjoint K k
  assert |- ( K e. V -> ( DIsoB ` K ) = ( w e. H |-> ( x e. dom ( ( DIsoA ` K ) ` w ) |-> ( ( ( ( DIsoA ` K ) ` w ) ` x ) X. { ( f e. ( ( LTrn ` K ) ` w ) |-> ( _I |` B ) ) } ) ) ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    cdib
    cfv
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
    @2
    cfv
    #
    vf
    @0
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
    wceq
    cK
    cV
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    vx
    @0
    @14
    cdia
    cfv
    #
    cfv
    #
    cdm
    #
    @4
    @17
    cfv
    #
    vf
    @0
    @14
    cltrn
    cfv
    #
    cfv
    #
    cid
    @14
    cbs
    cfv
    #
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
    @13
    cvv
    cdib
    @14
    cK
    wceq
    #
    vw
    @15
    @27
    cH
    @12
    @28
    @15
    cK
    clh
    cfv
    #
    cH
    @14
    cK
    clh
    fveq2
    dibval.h
    syl6eqr
    @28
    vx
    @18
    @26
    @3
    @11
    @28
    @17
    @2
    @28
    @0
    @16
    @1
    @14
    cK
    cdia
    fveq2
    fveq1d
    #
    dmeqd
    @28
    @19
    @5
    @25
    @10
    @28
    @4
    @17
    @2
    @30
    fveq1d
    @28
    @24
    @9
    @28
    vf
    @21
    @23
    @7
    @8
    @28
    @0
    @20
    @6
    @14
    cK
    cltrn
    fveq2
    fveq1d
    @28
    @22
    cB
    cid
    @28
    @22
    cK
    cbs
    cfv
    cB
    @14
    cK
    cbs
    fveq2
    dibval.b
    syl6eqr
    reseq2d
    mpteq12dv
    sneqd
    xpeq12d
    mpteq12dv
    mpteq12dv
    vx
    vw
    vf
    vk
    df-dib
    vw
    cH
    @12
    cH
    @29
    cvv
    dibval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
