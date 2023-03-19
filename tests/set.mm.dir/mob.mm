include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "cvv.mm"
include "elex.mm"
include "w3a.mm"
include "cv.mm"
include "nfv.mm"
include "nfmo1.mm"
include "nf3an.mm"
include "nfim.mm"
include "3anbi3d.mm"
include "eqeq1.mm"
include "bibi1d.mm"
include "imbi12d.mm"
include "mob2.mm"
include "vtoclg1f.mm"
include "com12.mm"
include "3expib.mm"
include "syl.mm"
include "com3r.mm"
include "imp.mm"
include "3impib.mm"

theorem mob
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
  assert |- ( ( ( A e. C /\ B e. D ) /\ E* x ph /\ ps ) -> ( A = B <-> ch ) )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    wph
    vx
    wmo
    #
    wps
    cA
    cB
    wceq
    #
    wch
    wb
    #
    @0
    @1
    @2
    wps
    wa
    #
    @4
    wi
    @1
    @5
    @0
    @4
    @1
    cB
    cvv
    wcel
    #
    @5
    @0
    @4
    wi
    #
    wi
    cB
    cD
    elex
    @6
    @2
    wps
    @7
    @0
    @6
    @2
    wps
    w3a
    #
    @4
    @6
    @2
    wph
    w3a
    #
    vx
    cv
    #
    cB
    wceq
    #
    wch
    wb
    #
    wi
    @8
    @4
    wi
    vx
    cA
    cC
    @8
    @4
    vx
    @6
    @2
    wps
    vx
    @6
    vx
    nfv
    wph
    vx
    nfmo1
    wps
    vx
    nfv
    nf3an
    @4
    vx
    nfv
    nfim
    @10
    cA
    wceq
    #
    @9
    @8
    @12
    @4
    @13
    wph
    wps
    @6
    @2
    moi.1
    3anbi3d
    @13
    @11
    @3
    wch
    @10
    cA
    cB
    eqeq1
    bibi1d
    imbi12d
    wph
    wch
    vx
    cB
    cvv
    moi.2
    mob2
    vtoclg1f
    com12
    3expib
    syl
    com3r
    imp
    3impib
end
