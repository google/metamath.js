include "wcel.mm"
include "cvv.mm"
include "cldil.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cmpt.mm"
include "elex.mm"
include "clh.mm"
include "cple.mm"
include "cbs.mm"
include "claut.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breqd.mm"
include "imbi1d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "df-ldil.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem ldilfset
  let vx: setvar x
  let vw: setvar w
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let vk: setvar k
  assume ldilset.b: |- B = ( Base ` K )
  assume ldilset.l: |- .<_ = ( le ` K )
  assume ldilset.h: |- H = ( LHyp ` K )
  assume ldilset.i: |- I = ( LAut ` K )

  disjoint B x
  disjoint H w
  disjoint I f
  disjoint f w
  disjoint f x
  disjoint K f
  disjoint w x
  disjoint K w
  disjoint K x
  disjoint k x
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint f k
  disjoint I k
  disjoint K k
  disjoint .<_ k
  assert |- ( K e. C -> ( LDil ` K ) = ( w e. H |-> { f e. I | A. x e. B ( x .<_ w -> ( f ` x ) = x ) } ) )

  proof
    cK
    cC
    wcel
    cK
    cvv
    wcel
    cK
    cldil
    cfv
    vw
    cH
    vx
    cv
    #
    vw
    cv
    #
    c.le
    wbr
    #
    @0
    vf
    cv
    cfv
    @0
    wceq
    #
    wi
    #
    vx
    cB
    wral
    #
    vf
    cI
    crab
    #
    cmpt
    #
    wceq
    cK
    cC
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
    @0
    @1
    @8
    cple
    cfv
    #
    wbr
    #
    @3
    wi
    #
    vx
    @8
    cbs
    cfv
    #
    wral
    #
    vf
    @8
    claut
    cfv
    #
    crab
    #
    cmpt
    @7
    cvv
    cldil
    @8
    cK
    wceq
    #
    vw
    @9
    @16
    cH
    @6
    @17
    @9
    cK
    clh
    cfv
    #
    cH
    @8
    cK
    clh
    fveq2
    ldilset.h
    syl6eqr
    @17
    @14
    @5
    vf
    @15
    cI
    @17
    @15
    cK
    claut
    cfv
    cI
    @8
    cK
    claut
    fveq2
    ldilset.i
    syl6eqr
    @17
    @12
    @4
    vx
    @13
    cB
    @17
    @13
    cK
    cbs
    cfv
    cB
    @8
    cK
    cbs
    fveq2
    ldilset.b
    syl6eqr
    @17
    @11
    @2
    @3
    @17
    @10
    c.le
    @0
    @1
    @17
    @10
    cK
    cple
    cfv
    c.le
    @8
    cK
    cple
    fveq2
    ldilset.l
    syl6eqr
    breqd
    imbi1d
    raleqbidv
    rabeqbidv
    mpteq12dv
    vx
    vw
    vf
    vk
    df-ldil
    vw
    cH
    @6
    cH
    @18
    cvv
    ldilset.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
