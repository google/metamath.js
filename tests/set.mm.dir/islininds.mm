include "cv.mm"
include "cbs.mm"
include "cfv.mm"
include "cpw.mm"
include "wcel.mm"
include "csca.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wi.mm"
include "cmap.mm"
include "clininds.mm"
include "simpl.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "pweqd.mm"
include "eleq12d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "breq2d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "eqeq2d.mm"
include "raleqbidv.mm"
include "imbi12d.mm"
include "df-lininds.mm"
include "brabga.mm"

theorem islininds
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cE: class E
  let cM: class M
  let cV: class V
  let cW: class W
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
  assert |- ( ( S e. V /\ M e. W ) -> ( S linIndS M <-> ( S e. ~P B /\ A. f e. ( E ^m S ) ( ( f finSupp .0. /\ ( f ( linC ` M ) S ) = Z ) -> A. x e. S ( f ` x ) = .0. ) ) ) )

  proof
    vs
    cv
    #
    vm
    cv
    #
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    vf
    cv
    #
    @1
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @5
    @0
    @1
    clinc
    cfv
    #
    co
    #
    @1
    c0g
    cfv
    #
    wceq
    #
    wa
    #
    vx
    cv
    @5
    cfv
    #
    @7
    wceq
    #
    vx
    @0
    wral
    #
    wi
    #
    vf
    @6
    cbs
    cfv
    #
    @0
    cmap
    co
    #
    wral
    #
    wa
    cS
    cB
    cpw
    #
    wcel
    #
    @5
    c.0
    cfsupp
    wbr
    #
    @5
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
    wa
    #
    @14
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
    cE
    cS
    cmap
    co
    #
    wral
    #
    wa
    vs
    vm
    cS
    cM
    clininds
    cV
    cW
    @0
    cS
    wceq
    #
    @1
    cM
    wceq
    #
    wa
    #
    @4
    @22
    @20
    @32
    @35
    @0
    cS
    @3
    @21
    @33
    @34
    simpl
    #
    @35
    @2
    cB
    @34
    @2
    cB
    wceq
    @33
    @34
    @2
    cM
    cbs
    cfv
    cB
    @1
    cM
    cbs
    fveq2
    islininds.b
    syl6eqr
    adantl
    pweqd
    eleq12d
    @35
    @17
    @30
    vf
    @19
    @31
    @35
    @18
    cE
    @0
    cS
    cmap
    @34
    @18
    cE
    wceq
    @33
    @34
    @18
    cR
    cbs
    cfv
    cE
    @34
    @6
    cR
    cbs
    @34
    @6
    cM
    csca
    cfv
    #
    cR
    @1
    cM
    csca
    fveq2
    #
    islininds.r
    syl6eqr
    #
    fveq2d
    islininds.e
    syl6eqr
    adantl
    @36
    oveq12d
    @35
    @13
    @27
    @16
    @29
    @35
    @8
    @23
    @12
    @26
    @35
    @7
    c.0
    @5
    cfsupp
    @35
    @7
    cR
    c0g
    cfv
    #
    c.0
    @35
    @6
    cR
    c0g
    @35
    @6
    @37
    cR
    @34
    @6
    @37
    wceq
    @33
    @38
    adantl
    islininds.r
    syl6eqr
    fveq2d
    islininds.0
    syl6eqr
    breq2d
    @35
    @10
    @25
    @11
    cZ
    @35
    @5
    @5
    @0
    cS
    @9
    @24
    @34
    @9
    @24
    wceq
    @33
    @1
    cM
    clinc
    fveq2
    adantl
    @35
    @5
    eqidd
    @36
    oveq123d
    @35
    @11
    cM
    c0g
    cfv
    #
    cZ
    @34
    @11
    @41
    wceq
    @33
    @1
    cM
    c0g
    fveq2
    adantl
    islininds.z
    syl6eqr
    eqeq12d
    anbi12d
    @35
    @15
    @28
    vx
    @0
    cS
    @36
    @35
    @7
    c.0
    @14
    @34
    @7
    c.0
    wceq
    @33
    @34
    @7
    @40
    c.0
    @34
    @6
    cR
    c0g
    @39
    fveq2d
    islininds.0
    syl6eqr
    adantl
    eqeq2d
    raleqbidv
    imbi12d
    raleqbidv
    anbi12d
    vx
    vf
    vm
    vs
    df-lininds
    brabga
end
