include "wcel.mm"
include "wa.mm"
include "cldil.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cmpt.mm"
include "ldilfset.mm"
include "fveq1d.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "eqid.mm"
include "claut.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "syl5eq.mm"

theorem ldilset
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  assume ldilset.b: |- B = ( Base ` K )
  assume ldilset.l: |- .<_ = ( le ` K )
  assume ldilset.h: |- H = ( LHyp ` K )
  assume ldilset.i: |- I = ( LAut ` K )
  assume ldilset.d: |- D = ( ( LDil ` K ) ` W )

  disjoint B x
  disjoint I f
  disjoint f x
  disjoint K f
  disjoint K x
  disjoint W f
  disjoint W x
  disjoint k x
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint I k
  disjoint f w
  disjoint K k
  disjoint w x
  disjoint K w
  disjoint .<_ k
  disjoint B w
  disjoint I w
  disjoint .<_ w
  disjoint W w
  assert |- ( ( K e. C /\ W e. H ) -> D = { f e. I | A. x e. B ( x .<_ W -> ( f ` x ) = x ) } )

  proof
    cK
    cC
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    cD
    cW
    cK
    cldil
    cfv
    #
    cfv
    #
    vx
    cv
    #
    cW
    c.le
    wbr
    #
    @4
    vf
    cv
    cfv
    @4
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
    ldilset.d
    @0
    @1
    @3
    cW
    vw
    cH
    @4
    vw
    cv
    #
    c.le
    wbr
    #
    @6
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
    cfv
    @9
    @0
    cW
    @2
    @15
    vx
    vw
    cB
    cC
    vf
    cH
    cI
    cK
    c.le
    ldilset.b
    ldilset.l
    ldilset.h
    ldilset.i
    ldilfset
    fveq1d
    vw
    cW
    @14
    @9
    cH
    @15
    @10
    cW
    wceq
    #
    @13
    @8
    vf
    cI
    @16
    @12
    @7
    vx
    cB
    @16
    @11
    @5
    @6
    @10
    cW
    @4
    c.le
    breq2
    imbi1d
    ralbidv
    rabbidv
    @15
    eqid
    @8
    vf
    cI
    cI
    cK
    claut
    cfv
    cvv
    ldilset.i
    cK
    claut
    fvex
    eqeltri
    rabex
    fvmpt
    sylan9eq
    syl5eq
end
