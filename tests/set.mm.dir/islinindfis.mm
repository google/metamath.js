include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "clininds.mm"
include "wbr.mm"
include "cpw.mm"
include "cv.mm"
include "cfsupp.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "islininds.mm"
include "wo.mm"
include "pm4.79.mm"
include "cvv.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "simpll.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fdmfifsupp.mm"
include "adantr.mm"
include "imim1i.mm"
include "expd.mm"
include "ax-1.mm"
include "jaoi.mm"
include "sylbir.mm"
include "com12.mm"
include "pm3.42.mm"
include "impbid1.mm"
include "ralbidva.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem islinindfis
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
  assert |- ( ( S e. Fin /\ M e. W ) -> ( S linIndS M <-> ( S e. ~P B /\ A. f e. ( E ^m S ) ( ( f ( linC ` M ) S ) = Z -> A. x e. S ( f ` x ) = .0. ) ) ) )

  proof
    cS
    cfn
    wcel
    #
    cM
    cW
    wcel
    #
    wa
    #
    cS
    cM
    clininds
    wbr
    cS
    cB
    cpw
    wcel
    #
    vf
    cv
    #
    c.0
    cfsupp
    wbr
    #
    @4
    cS
    cM
    clinc
    cfv
    co
    cZ
    wceq
    #
    wa
    vx
    cv
    @4
    cfv
    c.0
    wceq
    vx
    cS
    wral
    #
    wi
    #
    vf
    cE
    cS
    cmap
    co
    #
    wral
    #
    wa
    @3
    @6
    @7
    wi
    #
    vf
    @9
    wral
    #
    wa
    vx
    cB
    cR
    cS
    vf
    cE
    cM
    cfn
    cW
    c.0
    cZ
    islininds.b
    islininds.z
    islininds.r
    islininds.e
    islininds.0
    islininds
    @2
    @10
    @12
    @3
    @2
    @8
    @11
    vf
    @9
    @2
    @4
    @9
    wcel
    #
    wa
    #
    @8
    @11
    @8
    @14
    @11
    @8
    @5
    @7
    wi
    #
    @11
    wo
    @14
    @11
    wi
    #
    @7
    @5
    @6
    pm4.79
    @15
    @16
    @11
    @15
    @14
    @6
    @7
    @14
    @6
    wa
    @5
    @7
    @14
    @5
    @6
    @14
    cS
    cE
    @4
    cvv
    c.0
    @13
    cS
    cE
    @4
    wf
    @2
    @4
    cE
    cS
    elmapi
    adantl
    @0
    @1
    @13
    simpll
    c.0
    cvv
    wcel
    @14
    c.0
    cR
    c0g
    cfv
    cvv
    islininds.0
    cR
    c0g
    fvex
    eqeltri
    a1i
    fdmfifsupp
    adantr
    imim1i
    expd
    @11
    @14
    ax-1
    jaoi
    sylbir
    com12
    @5
    @6
    @7
    pm3.42
    impbid1
    ralbidva
    anbi2d
    bitrd
end
