include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "nfel1.mm"
include "nfv.mm"
include "nfan.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "vtocl2gf.mm"
include "pm2.43i.mm"

theorem vtocl2gaf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume vtocl2gaf.a: |- F/_ x A
  assume vtocl2gaf.b: |- F/_ y A
  assume vtocl2gaf.c: |- F/_ y B
  assume vtocl2gaf.1: |- F/ x ps
  assume vtocl2gaf.2: |- F/ y ch
  assume vtocl2gaf.3: |- ( x = A -> ( ph <-> ps ) )
  assume vtocl2gaf.4: |- ( y = B -> ( ps <-> ch ) )
  assume vtocl2gaf.5: |- ( ( x e. C /\ y e. D ) -> ph )

  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  assert |- ( ( A e. C /\ B e. D ) -> ch )

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
    #
    wch
    vx
    cv
    #
    cC
    wcel
    #
    vy
    cv
    #
    cD
    wcel
    #
    wa
    #
    wph
    wi
    @0
    @6
    wa
    #
    wps
    wi
    @2
    wch
    wi
    vx
    vy
    cA
    cB
    cC
    cD
    vtocl2gaf.a
    vtocl2gaf.b
    vtocl2gaf.c
    @8
    wps
    vx
    @0
    @6
    vx
    vx
    cA
    cC
    vtocl2gaf.a
    nfel1
    @6
    vx
    nfv
    nfan
    vtocl2gaf.1
    nfim
    @2
    wch
    vy
    @0
    @1
    vy
    vy
    cA
    cC
    vtocl2gaf.b
    nfel1
    vy
    cB
    cD
    vtocl2gaf.c
    nfel1
    nfan
    vtocl2gaf.2
    nfim
    @3
    cA
    wceq
    #
    @7
    @8
    wph
    wps
    @9
    @4
    @0
    @6
    @3
    cA
    cC
    eleq1
    anbi1d
    vtocl2gaf.3
    imbi12d
    @5
    cB
    wceq
    #
    @8
    @2
    wps
    wch
    @10
    @6
    @1
    @0
    @5
    cB
    cD
    eleq1
    anbi2d
    vtocl2gaf.4
    imbi12d
    vtocl2gaf.5
    vtocl2gf
    pm2.43i
end
