include "clininds.mm"
include "wbr.mm"
include "cpw.mm"
include "wcel.mm"
include "cv.mm"
include "cfsupp.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "cvv.mm"
include "wb.mm"
include "linindsv.mm"
include "islininds.mm"
include "syl.mm"
include "ibi.mm"

theorem linindsi
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cE: class E
  let cM: class M
  let c.0: class .0.
  let cZ: class Z
  let vm: setvar m
  let vs: setvar s
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
  disjoint k x
  assert |- ( S linIndS M -> ( S e. ~P B /\ A. f e. ( E ^m S ) ( ( f finSupp .0. /\ ( f ( linC ` M ) S ) = Z ) -> A. x e. S ( f ` x ) = .0. ) ) )

  proof
    cS
    cM
    clininds
    wbr
    #
    cS
    cB
    cpw
    wcel
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    @1
    cS
    cM
    clinc
    cfv
    co
    cZ
    wceq
    wa
    vx
    cv
    @1
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
    wa
    #
    @0
    cS
    cvv
    wcel
    cM
    cvv
    wcel
    wa
    @0
    @2
    wb
    cS
    cM
    linindsv
    vx
    cB
    cR
    cS
    vf
    cE
    cM
    cvv
    cvv
    c.0
    cZ
    islininds.b
    islininds.z
    islininds.r
    islininds.e
    islininds.0
    islininds
    syl
    ibi
end
