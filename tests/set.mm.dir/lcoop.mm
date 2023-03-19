include "wcel.mm"
include "cpw.mm"
include "wa.mm"
include "cvv.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "clinc.mm"
include "co.mm"
include "wceq.mm"
include "cmap.mm"
include "wrex.mm"
include "crab.mm"
include "clinco.mm"
include "elex.mm"
include "adantr.mm"
include "pweqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabexg.mm"
include "mp1i.mm"
include "csca.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "simpr.mm"
include "oveq12d.mm"
include "a1i.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "rabeqbidv.mm"
include "pweqd.mm"
include "df-lco.mm"
include "ovmpt2x.mm"
include "syl3anc.mm"

theorem lcoop
  let cB: class B
  let cR: class R
  let cS: class S
  let cM: class M
  let cV: class V
  let cX: class X
  let vs: setvar s
  let vc: setvar c
  let vm: setvar m
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x
  assume lcoop.b: |- B = ( Base ` M )
  assume lcoop.s: |- S = ( Scalar ` M )
  assume lcoop.r: |- R = ( Base ` S )

  disjoint B c
  disjoint M c
  disjoint M s
  disjoint c s
  disjoint R c
  disjoint R s
  disjoint V c
  disjoint V s
  disjoint B m
  disjoint B v
  disjoint c m
  disjoint c v
  disjoint m v
  disjoint M m
  disjoint M v
  disjoint m s
  disjoint s v
  disjoint R m
  disjoint R v
  disjoint S m
  disjoint S v
  disjoint V m
  disjoint V v
  disjoint k x
  assert |- ( ( M e. X /\ V e. ~P B ) -> ( M LinCo V ) = { c e. B | E. s e. ( R ^m V ) ( s finSupp ( 0g ` S ) /\ c = ( s ( linC ` M ) V ) ) } )

  proof
    cM
    cX
    wcel
    #
    cV
    cB
    cpw
    #
    wcel
    #
    wa
    #
    cM
    cvv
    wcel
    #
    cV
    cM
    cbs
    cfv
    #
    cpw
    #
    wcel
    #
    vs
    cv
    #
    cS
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    vc
    cv
    #
    @8
    cV
    cM
    clinc
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vs
    cR
    cV
    cmap
    co
    #
    wrex
    #
    vc
    cB
    crab
    #
    cvv
    wcel
    #
    cM
    cV
    clinco
    co
    @18
    wceq
    @0
    @4
    @2
    cM
    cX
    elex
    adantr
    @2
    @7
    @0
    @2
    @7
    @1
    @6
    cV
    cB
    @5
    lcoop.b
    pweqi
    eleq2i
    biimpi
    adantl
    cB
    cvv
    wcel
    @19
    @3
    cB
    @5
    cvv
    lcoop.b
    cM
    cbs
    fvex
    eqeltri
    @17
    vc
    cB
    cvv
    rabexg
    mp1i
    vm
    vv
    cM
    cV
    cvv
    vm
    cv
    #
    cbs
    cfv
    #
    cpw
    @8
    @20
    csca
    cfv
    #
    c0g
    cfv
    #
    cfsupp
    wbr
    #
    @11
    @8
    vv
    cv
    #
    @20
    clinc
    cfv
    #
    co
    #
    wceq
    #
    wa
    #
    vs
    @22
    cbs
    cfv
    #
    @25
    cmap
    co
    #
    wrex
    #
    vc
    @21
    crab
    @18
    clinco
    cvv
    @6
    @20
    cM
    wceq
    #
    @25
    cV
    wceq
    #
    wa
    #
    @32
    @17
    vc
    @21
    cB
    @33
    @21
    cB
    wceq
    @34
    @33
    @21
    @5
    cB
    @20
    cM
    cbs
    fveq2
    #
    lcoop.b
    syl6eqr
    adantr
    @35
    @29
    @15
    vs
    @31
    @16
    @35
    @30
    cR
    @25
    cV
    cmap
    @35
    @30
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    cR
    @33
    @30
    @38
    wceq
    @34
    @33
    @22
    @37
    cbs
    @20
    cM
    csca
    fveq2
    #
    fveq2d
    adantr
    cR
    cS
    cbs
    cfv
    @38
    lcoop.r
    cS
    @37
    cbs
    lcoop.s
    fveq2i
    eqtri
    syl6eqr
    @33
    @34
    simpr
    #
    oveq12d
    @35
    @24
    @10
    @28
    @14
    @35
    @23
    @9
    @8
    cfsupp
    @33
    @23
    @9
    wceq
    @34
    @33
    @23
    @37
    c0g
    cfv
    @9
    @33
    @22
    @37
    c0g
    @39
    fveq2d
    @33
    @37
    cS
    c0g
    @33
    cS
    @37
    cS
    @37
    wceq
    @33
    lcoop.s
    a1i
    eqcomd
    fveq2d
    eqtrd
    adantr
    breq2d
    @35
    @27
    @13
    @11
    @35
    @8
    @8
    @25
    cV
    @26
    @12
    @33
    @26
    @12
    wceq
    @34
    @20
    cM
    clinc
    fveq2
    adantr
    @35
    @8
    eqidd
    @40
    oveq123d
    eqeq2d
    anbi12d
    rexeqbidv
    rabeqbidv
    @33
    @21
    @5
    @36
    pweqd
    vv
    vm
    vs
    vc
    df-lco
    ovmpt2x
    syl3anc
end
