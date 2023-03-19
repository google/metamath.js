include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wceq.mm"
include "wi.mm"
include "w3a.mm"
include "mob.mm"
include "biimprd.mm"
include "3expia.mm"
include "impd.mm"
include "3impia.mm"

theorem moi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume moi.1: |- ( x = A -> ( ph <-> ps ) )
  assume moi.2: |- ( x = B -> ( ph <-> ch ) )

  disjoint A x
  disjoint B x
  disjoint ch x
  disjoint ps x
  assert |- ( ( ( A e. C /\ B e. D ) /\ E* x ph /\ ( ps /\ ch ) ) -> A = B )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    #
    wph
    vx
    wmo
    #
    wps
    wch
    wa
    cA
    cB
    wceq
    #
    @0
    @1
    wa
    wps
    wch
    @2
    @0
    @1
    wps
    wch
    @2
    wi
    @0
    @1
    wps
    w3a
    @2
    wch
    wph
    wps
    wch
    vx
    cA
    cB
    cC
    cD
    moi.1
    moi.2
    mob
    biimprd
    3expia
    impd
    3impia
end
