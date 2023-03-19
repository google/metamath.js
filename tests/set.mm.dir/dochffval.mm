include "wcel.mm"
include "cvv.mm"
include "coch.mm"
include "cfv.mm"
include "cv.mm"
include "cdvh.mm"
include "cbs.mm"
include "cpw.mm"
include "cdih.mm"
include "wss.mm"
include "crab.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "clh.mm"
include "cglb.mm"
include "coc.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "pweqd.mm"
include "sseq2d.mm"
include "rabeqbidv.mm"
include "fveq12d.mm"
include "mpteq12dv.mm"
include "df-doch.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem dochffval
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cB: class B
  let cG: class G
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let vk: setvar k
  assume dochval.b: |- B = ( Base ` K )
  assume dochval.g: |- G = ( glb ` K )
  assume dochval.o: |- ._|_ = ( oc ` K )
  assume dochval.h: |- H = ( LHyp ` K )

  disjoint B y
  disjoint H w
  disjoint w x
  disjoint w y
  disjoint K w
  disjoint x y
  disjoint K x
  disjoint K y
  disjoint k y
  disjoint B k
  disjoint G k
  disjoint k w
  disjoint H k
  disjoint k x
  disjoint K k
  disjoint ._|_ k
  assert |- ( K e. V -> ( ocH ` K ) = ( w e. H |-> ( x e. ~P ( Base ` ( ( DVecH ` K ) ` w ) ) |-> ( ( ( DIsoH ` K ) ` w ) ` ( ._|_ ` ( G ` { y e. B | x C_ ( ( ( DIsoH ` K ) ` w ) ` y ) } ) ) ) ) ) )

  proof
    cK
    cV
    wcel
    cK
    cvv
    wcel
    cK
    coch
    cfv
    vw
    cH
    vx
    vw
    cv
    #
    cK
    cdvh
    cfv
    #
    cfv
    #
    cbs
    cfv
    #
    cpw
    #
    vx
    cv
    #
    vy
    cv
    #
    @0
    cK
    cdih
    cfv
    #
    cfv
    #
    cfv
    #
    wss
    #
    vy
    cB
    crab
    #
    cG
    cfv
    #
    c.pe
    cfv
    #
    @8
    cfv
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
    @17
    cdvh
    cfv
    #
    cfv
    #
    cbs
    cfv
    #
    cpw
    #
    @5
    @6
    @0
    @17
    cdih
    cfv
    #
    cfv
    #
    cfv
    #
    wss
    #
    vy
    @17
    cbs
    cfv
    #
    crab
    #
    @17
    cglb
    cfv
    #
    cfv
    #
    @17
    coc
    cfv
    #
    cfv
    #
    @24
    cfv
    #
    cmpt
    #
    cmpt
    @16
    cvv
    coch
    @17
    cK
    wceq
    #
    vw
    @18
    @34
    cH
    @15
    @35
    @18
    cK
    clh
    cfv
    #
    cH
    @17
    cK
    clh
    fveq2
    dochval.h
    syl6eqr
    @35
    vx
    @22
    @33
    @4
    @14
    @35
    @21
    @3
    @35
    @20
    @2
    cbs
    @35
    @0
    @19
    @1
    @17
    cK
    cdvh
    fveq2
    fveq1d
    fveq2d
    pweqd
    @35
    @32
    @13
    @24
    @8
    @35
    @0
    @23
    @7
    @17
    cK
    cdih
    fveq2
    fveq1d
    #
    @35
    @30
    @12
    @31
    c.pe
    @35
    @31
    cK
    coc
    cfv
    c.pe
    @17
    cK
    coc
    fveq2
    dochval.o
    syl6eqr
    @35
    @28
    @11
    @29
    cG
    @35
    @29
    cK
    cglb
    cfv
    cG
    @17
    cK
    cglb
    fveq2
    dochval.g
    syl6eqr
    @35
    @26
    @10
    vy
    @27
    cB
    @35
    @27
    cK
    cbs
    cfv
    cB
    @17
    cK
    cbs
    fveq2
    dochval.b
    syl6eqr
    @35
    @25
    @9
    @5
    @35
    @6
    @24
    @8
    @37
    fveq1d
    sseq2d
    rabeqbidv
    fveq12d
    fveq12d
    fveq12d
    mpteq12dv
    mpteq12dv
    vx
    vy
    vw
    vk
    df-doch
    vw
    cH
    @15
    cH
    @36
    cvv
    dochval.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
