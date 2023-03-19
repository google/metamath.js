include "cmgm.mm"
include "wcel.mm"
include "csubmgm.mm"
include "cfv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cbs.mm"
include "cpw.mm"
include "crab.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "fveq2.mm"
include "pweqd.mm"
include "oveqd.mm"
include "eleq1d.mm"
include "2ralbidv.mm"
include "rabeqbidv.mm"
include "df-submgm.mm"
include "fvex.mm"
include "pwex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "eleq2d.mm"
include "elpw2.mm"
include "anbi1i.mm"
include "eleq2.mm"
include "raleqbi1dv.mm"
include "elrab.mm"
include "sseq2i.mm"
include "oveqi.mm"
include "eleq1i.mm"
include "2ralbii.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "syl6bb.mm"

theorem issubmgm
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cM: class M
  let vm: setvar m
  let vt: setvar t
  let vk: setvar k
  assume issubmgm.b: |- B = ( Base ` M )
  assume issubmgm.p: |- .+ = ( +g ` M )

  disjoint M x
  disjoint M y
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint M m
  disjoint M t
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint t x
  disjoint t y
  disjoint S t
  disjoint k x
  assert |- ( M e. Mgm -> ( S e. ( SubMgm ` M ) <-> ( S C_ B /\ A. x e. S A. y e. S ( x .+ y ) e. S ) ) )

  proof
    cM
    cmgm
    wcel
    #
    cS
    cM
    csubmgm
    cfv
    #
    wcel
    cS
    vx
    cv
    #
    vy
    cv
    #
    cM
    cplusg
    cfv
    #
    co
    #
    vt
    cv
    #
    wcel
    #
    vy
    @6
    wral
    #
    vx
    @6
    wral
    #
    vt
    cM
    cbs
    cfv
    #
    cpw
    #
    crab
    #
    wcel
    #
    cS
    cB
    wss
    #
    @2
    @3
    c.pl
    co
    #
    cS
    wcel
    #
    vy
    cS
    wral
    vx
    cS
    wral
    #
    wa
    #
    @0
    @1
    @12
    cS
    vm
    cM
    @2
    @3
    vm
    cv
    #
    cplusg
    cfv
    #
    co
    #
    @6
    wcel
    #
    vy
    @6
    wral
    vx
    @6
    wral
    #
    vt
    @19
    cbs
    cfv
    #
    cpw
    #
    crab
    @12
    cmgm
    csubmgm
    @19
    cM
    wceq
    #
    @23
    @9
    vt
    @25
    @11
    @26
    @24
    @10
    @19
    cM
    cbs
    fveq2
    pweqd
    @26
    @22
    @7
    vx
    vy
    @6
    @6
    @26
    @21
    @5
    @6
    @26
    @20
    @4
    @2
    @3
    @19
    cM
    cplusg
    fveq2
    oveqd
    eleq1d
    2ralbidv
    rabeqbidv
    vx
    vy
    vt
    vm
    df-submgm
    @9
    vt
    @11
    @10
    cM
    cbs
    fvex
    #
    pwex
    rabex
    fvmpt
    eleq2d
    cS
    @11
    wcel
    #
    @5
    cS
    wcel
    #
    vy
    cS
    wral
    #
    vx
    cS
    wral
    #
    wa
    cS
    @10
    wss
    #
    @31
    wa
    @13
    @18
    @28
    @32
    @31
    cS
    @10
    @27
    elpw2
    anbi1i
    @9
    @31
    vt
    cS
    @11
    @8
    @30
    vx
    @6
    cS
    @7
    @29
    vy
    @6
    cS
    @6
    cS
    @5
    eleq2
    raleqbi1dv
    raleqbi1dv
    elrab
    @14
    @32
    @17
    @31
    cB
    @10
    cS
    issubmgm.b
    sseq2i
    @16
    @29
    vx
    vy
    cS
    cS
    @15
    @5
    cS
    c.pl
    @4
    @2
    @3
    issubmgm.p
    oveqi
    eleq1i
    2ralbii
    anbi12i
    3bitr4i
    syl6bb
end
