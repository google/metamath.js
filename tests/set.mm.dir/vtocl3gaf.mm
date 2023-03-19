include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "wi.mm"
include "nfel1.mm"
include "nfv.mm"
include "nf3an.mm"
include "nfim.mm"
include "wceq.mm"
include "eleq1.mm"
include "3anbi1d.mm"
include "imbi12d.mm"
include "3anbi2d.mm"
include "3anbi3d.mm"
include "vtocl3gf.mm"
include "pm2.43i.mm"

theorem vtocl3gaf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cT: class T
  assume vtocl3gaf.a: |- F/_ x A
  assume vtocl3gaf.b: |- F/_ y A
  assume vtocl3gaf.c: |- F/_ z A
  assume vtocl3gaf.d: |- F/_ y B
  assume vtocl3gaf.e: |- F/_ z B
  assume vtocl3gaf.f: |- F/_ z C
  assume vtocl3gaf.1: |- F/ x ps
  assume vtocl3gaf.2: |- F/ y ch
  assume vtocl3gaf.3: |- F/ z th
  assume vtocl3gaf.4: |- ( x = A -> ( ph <-> ps ) )
  assume vtocl3gaf.5: |- ( y = B -> ( ps <-> ch ) )
  assume vtocl3gaf.6: |- ( z = C -> ( ch <-> th ) )
  assume vtocl3gaf.7: |- ( ( x e. R /\ y e. S /\ z e. T ) -> ph )

  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T x
  disjoint T y
  disjoint T z
  assert |- ( ( A e. R /\ B e. S /\ C e. T ) -> th )

  proof
    cA
    cR
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cT
    wcel
    #
    w3a
    #
    wth
    vx
    cv
    #
    cR
    wcel
    #
    vy
    cv
    #
    cS
    wcel
    #
    vz
    cv
    #
    cT
    wcel
    #
    w3a
    #
    wph
    wi
    @0
    @7
    @9
    w3a
    #
    wps
    wi
    @0
    @1
    @9
    w3a
    #
    wch
    wi
    @3
    wth
    wi
    vx
    vy
    vz
    cA
    cB
    cC
    cR
    cS
    cT
    vtocl3gaf.a
    vtocl3gaf.b
    vtocl3gaf.c
    vtocl3gaf.d
    vtocl3gaf.e
    vtocl3gaf.f
    @11
    wps
    vx
    @0
    @7
    @9
    vx
    vx
    cA
    cR
    vtocl3gaf.a
    nfel1
    @7
    vx
    nfv
    @9
    vx
    nfv
    nf3an
    vtocl3gaf.1
    nfim
    @12
    wch
    vy
    @0
    @1
    @9
    vy
    vy
    cA
    cR
    vtocl3gaf.b
    nfel1
    vy
    cB
    cS
    vtocl3gaf.d
    nfel1
    @9
    vy
    nfv
    nf3an
    vtocl3gaf.2
    nfim
    @3
    wth
    vz
    @0
    @1
    @2
    vz
    vz
    cA
    cR
    vtocl3gaf.c
    nfel1
    vz
    cB
    cS
    vtocl3gaf.e
    nfel1
    vz
    cC
    cT
    vtocl3gaf.f
    nfel1
    nf3an
    vtocl3gaf.3
    nfim
    @4
    cA
    wceq
    #
    @10
    @11
    wph
    wps
    @13
    @5
    @0
    @7
    @9
    @4
    cA
    cR
    eleq1
    3anbi1d
    vtocl3gaf.4
    imbi12d
    @6
    cB
    wceq
    #
    @11
    @12
    wps
    wch
    @14
    @7
    @1
    @0
    @9
    @6
    cB
    cS
    eleq1
    3anbi2d
    vtocl3gaf.5
    imbi12d
    @8
    cC
    wceq
    #
    @12
    @3
    wch
    wth
    @15
    @9
    @2
    @0
    @1
    @8
    cC
    cT
    eleq1
    3anbi3d
    vtocl3gaf.6
    imbi12d
    vtocl3gaf.7
    vtocl3gf
    pm2.43i
end
