include "clininds.mm"
include "wbr.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cfsupp.mm"
include "clinc.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "wral.mm"
include "cpw.mm"
include "wa.mm"
include "wi.mm"
include "linindsi.mm"
include "breq1.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "fveq1.mm"
include "ralbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "com23.mm"
include "3impib.mm"
include "com12.mm"
include "adantl.mm"
include "syl.mm"
include "imp.mm"

theorem linindslinci
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let cE: class E
  let cF: class F
  let cM: class M
  let c.0: class .0.
  let cZ: class Z
  let vm: setvar m
  let vs: setvar s
  let vf: setvar f
  let vk: setvar k
  assume islininds.b: |- B = ( Base ` M )
  assume islininds.z: |- Z = ( 0g ` M )
  assume islininds.r: |- R = ( Scalar ` M )
  assume islininds.e: |- E = ( Base ` R )
  assume islininds.0: |- .0. = ( 0g ` R )

  disjoint M x
  disjoint S x
  disjoint F x
  disjoint B m
  disjoint B s
  disjoint m s
  disjoint E f
  disjoint E m
  disjoint E s
  disjoint f m
  disjoint f s
  disjoint M f
  disjoint M m
  disjoint M s
  disjoint f x
  disjoint m x
  disjoint s x
  disjoint S f
  disjoint S m
  disjoint S s
  disjoint Z m
  disjoint Z s
  disjoint .0. m
  disjoint .0. s
  disjoint F f
  disjoint .0. f
  disjoint Z f
  disjoint k x
  assert |- ( ( S linIndS M /\ ( F e. ( E ^m S ) /\ F finSupp .0. /\ ( F ( linC ` M ) S ) = Z ) ) -> A. x e. S ( F ` x ) = .0. )

  proof
    cS
    cM
    clininds
    wbr
    #
    cF
    cE
    cS
    cmap
    co
    #
    wcel
    #
    cF
    c.0
    cfsupp
    wbr
    #
    cF
    cS
    cM
    clinc
    cfv
    #
    co
    #
    cZ
    wceq
    #
    w3a
    #
    vx
    cv
    #
    cF
    cfv
    #
    c.0
    wceq
    #
    vx
    cS
    wral
    #
    @0
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
    @13
    cS
    @4
    co
    #
    cZ
    wceq
    #
    wa
    #
    @8
    @13
    cfv
    #
    c.0
    wceq
    #
    vx
    cS
    wral
    #
    wi
    #
    vf
    @1
    wral
    #
    wa
    @7
    @11
    wi
    #
    vx
    cB
    cR
    cS
    vf
    cE
    cM
    c.0
    cZ
    islininds.b
    islininds.z
    islininds.r
    islininds.e
    islininds.0
    linindsi
    @22
    @23
    @12
    @7
    @22
    @11
    @2
    @3
    @6
    @22
    @11
    wi
    @2
    @22
    @3
    @6
    wa
    #
    @11
    @21
    @24
    @11
    wi
    vf
    cF
    @1
    @13
    cF
    wceq
    #
    @17
    @24
    @20
    @11
    @25
    @14
    @3
    @16
    @6
    @13
    cF
    c.0
    cfsupp
    breq1
    @25
    @15
    @5
    cZ
    @13
    cF
    cS
    @4
    oveq1
    eqeq1d
    anbi12d
    @25
    @19
    @10
    vx
    cS
    @25
    @18
    @9
    c.0
    @8
    @13
    cF
    fveq1
    eqeq1d
    ralbidv
    imbi12d
    rspcv
    com23
    3impib
    com12
    adantl
    syl
    imp
end
