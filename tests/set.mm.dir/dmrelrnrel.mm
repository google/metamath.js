include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "id.mm"
include "jca31.mm"
include "wi.mm"
include "cv.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "breq2.mm"
include "fveq2.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "anbi1d.mm"
include "breq1.mm"
include "breq1d.mm"
include "wral.mm"
include "r19.21bi.mm"
include "vtoclg1f.mm"
include "sylc.mm"
include "mp2d.mm"

theorem dmrelrnrel
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cF: class F
  assume dmrelrnrel.x: |- F/ x ph
  assume dmrelrnrel.y: |- F/ y ph
  assume dmrelrnrel.i: |- ( ph -> A. x e. A A. y e. A ( x R y -> ( F ` x ) S ( F ` y ) ) )
  assume dmrelrnrel.b: |- ( ph -> B e. A )
  assume dmrelrnrel.c: |- ( ph -> C e. A )
  assume dmrelrnrel.r: |- ( ph -> B R C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint R x
  disjoint R y
  disjoint S x
  disjoint S y
  assert |- ( ph -> ( F ` B ) S ( F ` C ) )

  proof
    wph
    wph
    cB
    cA
    wcel
    #
    wa
    #
    cC
    cA
    wcel
    #
    wa
    #
    cB
    cC
    cR
    wbr
    #
    cB
    cF
    cfv
    #
    cC
    cF
    cfv
    #
    cS
    wbr
    #
    wph
    wph
    @0
    @2
    wph
    id
    dmrelrnrel.b
    dmrelrnrel.c
    jca31
    dmrelrnrel.r
    wph
    @2
    @0
    @3
    @4
    @7
    wi
    #
    wi
    #
    dmrelrnrel.c
    dmrelrnrel.b
    @0
    @1
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    cB
    @10
    cR
    wbr
    #
    @5
    @10
    cF
    cfv
    #
    cS
    wbr
    #
    wi
    #
    wi
    #
    wi
    @0
    @9
    wi
    vy
    cC
    cA
    @0
    @9
    vy
    @0
    vy
    nfv
    #
    @3
    @8
    vy
    @1
    @2
    vy
    wph
    @0
    vy
    dmrelrnrel.y
    @18
    nfan
    @2
    vy
    nfv
    nfan
    @8
    vy
    nfv
    nfim
    nfim
    @10
    cC
    wceq
    #
    @17
    @9
    @0
    @19
    @12
    @3
    @16
    @8
    @19
    @11
    @2
    @1
    @10
    cC
    cA
    eleq1
    anbi2d
    @19
    @13
    @4
    @15
    @7
    @10
    cC
    cB
    cR
    breq2
    @19
    @14
    @6
    @5
    cS
    @10
    cC
    cF
    fveq2
    breq2d
    imbi12d
    imbi12d
    imbi2d
    wph
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    @11
    wa
    #
    @20
    @10
    cR
    wbr
    #
    @20
    cF
    cfv
    #
    @14
    cS
    wbr
    #
    wi
    #
    wi
    @17
    vx
    cB
    cA
    @12
    @16
    vx
    @1
    @11
    vx
    wph
    @0
    vx
    dmrelrnrel.x
    @0
    vx
    nfv
    nfan
    @11
    vx
    nfv
    nfan
    @16
    vx
    nfv
    nfim
    @20
    cB
    wceq
    #
    @23
    @12
    @27
    @16
    @28
    @22
    @1
    @11
    @28
    @21
    @0
    wph
    @20
    cB
    cA
    eleq1
    anbi2d
    anbi1d
    @28
    @24
    @13
    @26
    @15
    @20
    cB
    @10
    cR
    breq1
    @28
    @25
    @5
    @14
    cS
    @20
    cB
    cF
    fveq2
    breq1d
    imbi12d
    imbi12d
    @22
    @27
    vy
    cA
    wph
    @27
    vy
    cA
    wral
    vx
    cA
    dmrelrnrel.i
    r19.21bi
    r19.21bi
    vtoclg1f
    vtoclg1f
    sylc
    mp2d
end
