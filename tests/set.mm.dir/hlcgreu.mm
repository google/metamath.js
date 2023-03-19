include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "hlcgrex.mm"
include "wcel.mm"
include "ad3antrrr.mm"
include "cstrkg.mm"
include "wne.mm"
include "simpllr.mm"
include "simplr.mm"
include "simprll.mm"
include "simprrl.mm"
include "simprlr.mm"
include "simprrr.mm"
include "hlcgreulem.mm"
include "ex.mm"
include "ralrimiva.mm"
include "jca.mm"
include "breq1.mm"
include "oveq2.mm"
include "eqidd.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "reu4.mm"
include "sylibr.mm"

theorem hlcgreu
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cG: class G
  let cI: class I
  let cK: class K
  let c.mi: class .-
  let vy: setvar y
  assume ishlg.p: |- P = ( Base ` G )
  assume ishlg.i: |- I = ( Itv ` G )
  assume ishlg.k: |- K = ( hlG ` G )
  assume ishlg.a: |- ( ph -> A e. P )
  assume ishlg.b: |- ( ph -> B e. P )
  assume ishlg.c: |- ( ph -> C e. P )
  assume hlln.1: |- ( ph -> G e. TarskiG )
  assume hltr.d: |- ( ph -> D e. P )
  assume hlcgrex.m: |- .- = ( dist ` G )
  assume hlcgrex.1: |- ( ph -> D =/= A )
  assume hlcgrex.2: |- ( ph -> B =/= C )

  disjoint .- x
  disjoint A x
  disjoint B x
  disjoint C x
  disjoint D x
  disjoint K x
  disjoint I x
  disjoint P x
  disjoint ph x
  disjoint .- y
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  disjoint D y
  disjoint K y
  disjoint I y
  disjoint P y
  disjoint ph y
  assert |- ( ph -> E! x e. P ( x ( K ` A ) D /\ ( A .- x ) = ( B .- C ) ) )

  proof
    wph
    vx
    cv
    #
    cD
    cA
    cK
    cfv
    #
    wbr
    #
    cA
    @0
    c.mi
    co
    #
    cB
    cC
    c.mi
    co
    #
    wceq
    #
    wa
    #
    vx
    cP
    wrex
    #
    @6
    vy
    cv
    #
    cD
    @1
    wbr
    #
    cA
    @8
    c.mi
    co
    #
    @4
    wceq
    #
    wa
    #
    wa
    #
    @0
    @8
    wceq
    #
    wi
    #
    vy
    cP
    wral
    #
    vx
    cP
    wral
    #
    wa
    @6
    vx
    cP
    wreu
    wph
    @7
    @17
    wph
    vx
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    cK
    c.mi
    ishlg.p
    ishlg.i
    ishlg.k
    ishlg.a
    ishlg.b
    ishlg.c
    hlln.1
    hltr.d
    hlcgrex.m
    hlcgrex.1
    hlcgrex.2
    hlcgrex
    wph
    @16
    vx
    cP
    wph
    @0
    cP
    wcel
    #
    wa
    #
    @15
    vy
    cP
    @19
    @8
    cP
    wcel
    #
    wa
    #
    @13
    @14
    @21
    @13
    wa
    cA
    cB
    cC
    cD
    cP
    cG
    cI
    cK
    c.mi
    @0
    @8
    ishlg.p
    ishlg.i
    ishlg.k
    wph
    cA
    cP
    wcel
    @18
    @20
    @13
    ishlg.a
    ad3antrrr
    wph
    cB
    cP
    wcel
    @18
    @20
    @13
    ishlg.b
    ad3antrrr
    wph
    cC
    cP
    wcel
    @18
    @20
    @13
    ishlg.c
    ad3antrrr
    wph
    cG
    cstrkg
    wcel
    @18
    @20
    @13
    hlln.1
    ad3antrrr
    wph
    cD
    cP
    wcel
    @18
    @20
    @13
    hltr.d
    ad3antrrr
    hlcgrex.m
    wph
    cD
    cA
    wne
    @18
    @20
    @13
    hlcgrex.1
    ad3antrrr
    wph
    cB
    cC
    wne
    @18
    @20
    @13
    hlcgrex.2
    ad3antrrr
    wph
    @18
    @20
    @13
    simpllr
    @19
    @20
    @13
    simplr
    @21
    @2
    @5
    @12
    simprll
    @21
    @6
    @9
    @11
    simprrl
    @21
    @2
    @5
    @12
    simprlr
    @21
    @6
    @9
    @11
    simprrr
    hlcgreulem
    ex
    ralrimiva
    ralrimiva
    jca
    @6
    @12
    vx
    vy
    cP
    @14
    @2
    @9
    @5
    @11
    @0
    @8
    cD
    @1
    breq1
    @14
    @3
    @10
    @4
    @4
    @0
    @8
    cA
    c.mi
    oveq2
    @14
    @4
    eqidd
    eqeq12d
    anbi12d
    reu4
    sylibr
end
