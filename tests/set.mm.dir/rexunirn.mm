include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "crn.mm"
include "cuni.mm"
include "df-rex.mm"
include "19.42v.mm"
include "anbi2i.mm"
include "bitr4i.mm"
include "exbii.mm"
include "elrnmpt1.mm"
include "mpdan.mm"
include "wceq.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "rspcev.mm"
include "sylan.mm"
include "r19.41v.mm"
include "sylib.mm"
include "eximi.mm"
include "eluni2.mm"
include "anbi1i.mm"
include "bitri.mm"
include "sylibr.mm"
include "exlimiv.mm"
include "sylbi.mm"

theorem rexunirn
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vb: setvar b
  assume rexunirn.1: |- F = ( x e. A |-> B )
  assume rexunirn.2: |- ( x e. A -> B e. V )

  disjoint x y
  disjoint A y
  disjoint F x
  disjoint ph x
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint F b
  disjoint b ph
  assert |- ( E. x e. A E. y e. B ph -> E. y e. U. ran F ph )

  proof
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wrex
    #
    vx
    cv
    cA
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wph
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    wph
    vy
    cF
    crn
    #
    cuni
    #
    wrex
    #
    @1
    @2
    @0
    wa
    #
    vx
    wex
    @8
    @0
    vx
    cA
    df-rex
    @7
    @12
    vx
    @7
    @2
    @5
    vy
    wex
    #
    wa
    @12
    @2
    @5
    vy
    19.42v
    @0
    @13
    @2
    wph
    vy
    cB
    df-rex
    anbi2i
    bitr4i
    exbii
    bitr4i
    @7
    @11
    vx
    @7
    @3
    vb
    cv
    #
    wcel
    #
    vb
    @9
    wrex
    #
    wph
    wa
    #
    vy
    wex
    #
    @11
    @6
    @17
    vy
    @6
    @15
    wph
    wa
    #
    vb
    @9
    wrex
    #
    @17
    @2
    cB
    @9
    wcel
    #
    @5
    @20
    @2
    cB
    cV
    wcel
    @21
    rexunirn.2
    vx
    cA
    cB
    cF
    cV
    rexunirn.1
    elrnmpt1
    mpdan
    @19
    @5
    vb
    cB
    @9
    @14
    cB
    wceq
    @15
    @4
    wph
    @14
    cB
    @3
    eleq2
    anbi1d
    rspcev
    sylan
    @15
    wph
    vb
    @9
    r19.41v
    sylib
    eximi
    @11
    @3
    @10
    wcel
    #
    wph
    wa
    #
    vy
    wex
    @18
    wph
    vy
    @10
    df-rex
    @23
    @17
    vy
    @22
    @16
    wph
    vb
    @3
    @9
    eluni2
    anbi1i
    exbii
    bitri
    sylibr
    exlimiv
    sylbi
end
