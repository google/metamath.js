include "catm.mm"
include "cfv.mm"
include "cdvh.mm"
include "clsa.mm"
include "clss.mm"
include "cple.mm"
include "cmee.mm"
include "eqid.mm"
include "dihglblem6.mm"

theorem dihglb
  let vx: setvar x
  let cB: class B
  let cS: class S
  let cG: class G
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  assume dihglb.b: |- B = ( Base ` K )
  assume dihglb.g: |- G = ( glb ` K )
  assume dihglb.h: |- H = ( LHyp ` K )
  assume dihglb.i: |- I = ( ( DIsoH ` K ) ` W )

  disjoint G x
  disjoint H x
  disjoint W x
  disjoint B x
  disjoint I x
  disjoint K x
  disjoint S x
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( S C_ B /\ S =/= (/) ) ) -> ( I ` ( G ` S ) ) = |^|_ x e. S ( I ` x ) )

  proof
    vx
    cK
    catm
    cfv
    #
    cB
    cW
    cK
    cdvh
    cfv
    cfv
    #
    clsa
    cfv
    #
    @1
    clss
    cfv
    #
    cS
    @1
    cG
    cH
    cI
    cK
    cK
    cple
    cfv
    #
    cK
    cmee
    cfv
    #
    cW
    dihglb.b
    @4
    eqid
    @5
    eqid
    @0
    eqid
    dihglb.g
    dihglb.h
    dihglb.i
    @1
    eqid
    @3
    eqid
    @2
    eqid
    dihglblem6
end
