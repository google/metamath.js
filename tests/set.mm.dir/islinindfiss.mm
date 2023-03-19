include "wcel.mm"
include "cfn.mm"
include "cpw.mm"
include "clininds.mm"
include "wbr.mm"
include "cv.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "wa.mm"
include "wb.mm"
include "islinindfis.mm"
include "ancoms.mm"
include "3adant3.mm"
include "3anibar.mm"

theorem islinindfiss
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cE: class E
  let cM: class M
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vm: setvar m
  let vs: setvar s
  let cF: class F
  let vk: setvar k
  assume islininds.b: |- B = ( Base ` M )
  assume islininds.z: |- Z = ( 0g ` M )
  assume islininds.r: |- R = ( Scalar ` M )
  assume islininds.e: |- E = ( Base ` R )
  assume islininds.0: |- .0. = ( 0g ` R )

  disjoint E f
  disjoint M f
  disjoint M x
  disjoint f x
  disjoint S f
  disjoint S x
  disjoint .0. f
  disjoint Z f
  disjoint W f
  disjoint B m
  disjoint B s
  disjoint m s
  disjoint E m
  disjoint E s
  disjoint f m
  disjoint f s
  disjoint M m
  disjoint M s
  disjoint m x
  disjoint s x
  disjoint S m
  disjoint S s
  disjoint Z m
  disjoint Z s
  disjoint .0. m
  disjoint .0. s
  disjoint F x
  disjoint F f
  disjoint k x
  assert |- ( ( M e. W /\ S e. Fin /\ S e. ~P B ) -> ( S linIndS M <-> A. f e. ( E ^m S ) ( ( f ( linC ` M ) S ) = Z -> A. x e. S ( f ` x ) = .0. ) ) )

  proof
    cM
    cW
    wcel
    #
    cS
    cfn
    wcel
    #
    cS
    cB
    cpw
    wcel
    #
    cS
    cM
    clininds
    wbr
    #
    vf
    cv
    #
    cS
    cM
    clinc
    cfv
    co
    cZ
    wceq
    vx
    cv
    @4
    cfv
    c.0
    wceq
    vx
    cS
    wral
    wi
    vf
    cE
    cS
    cmap
    co
    wral
    #
    @0
    @1
    @3
    @2
    @5
    wa
    wb
    #
    @2
    @1
    @0
    @6
    vx
    cB
    cR
    cS
    vf
    cE
    cM
    cW
    c.0
    cZ
    islininds.b
    islininds.z
    islininds.r
    islininds.e
    islininds.0
    islinindfis
    ancoms
    3adant3
    3anibar
end
