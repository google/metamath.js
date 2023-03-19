include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "elex.mm"
include "wi.mm"
include "nfel1.mm"
include "nfim.mm"
include "cv.mm"
include "wceq.mm"
include "imbi2d.mm"
include "vtoclgf.mm"
include "vtocl2gf.mm"
include "mpan9.mm"
include "3impb.mm"

theorem vtocl3gf
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
  let cV: class V
  let cW: class W
  let cX: class X
  assume vtocl3gf.a: |- F/_ x A
  assume vtocl3gf.b: |- F/_ y A
  assume vtocl3gf.c: |- F/_ z A
  assume vtocl3gf.d: |- F/_ y B
  assume vtocl3gf.e: |- F/_ z B
  assume vtocl3gf.f: |- F/_ z C
  assume vtocl3gf.1: |- F/ x ps
  assume vtocl3gf.2: |- F/ y ch
  assume vtocl3gf.3: |- F/ z th
  assume vtocl3gf.4: |- ( x = A -> ( ph <-> ps ) )
  assume vtocl3gf.5: |- ( y = B -> ( ps <-> ch ) )
  assume vtocl3gf.6: |- ( z = C -> ( ch <-> th ) )
  assume vtocl3gf.7: |- ph


  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> th )

  proof
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    cC
    cX
    wcel
    #
    wth
    @0
    cA
    cvv
    wcel
    #
    @1
    @2
    wa
    wth
    cA
    cV
    elex
    @3
    wps
    wi
    @3
    wch
    wi
    @3
    wth
    wi
    vy
    vz
    cB
    cC
    cW
    cX
    vtocl3gf.d
    vtocl3gf.e
    vtocl3gf.f
    @3
    wch
    vy
    vy
    cA
    cvv
    vtocl3gf.b
    nfel1
    vtocl3gf.2
    nfim
    @3
    wth
    vz
    vz
    cA
    cvv
    vtocl3gf.c
    nfel1
    vtocl3gf.3
    nfim
    vy
    cv
    cB
    wceq
    wps
    wch
    @3
    vtocl3gf.5
    imbi2d
    vz
    cv
    cC
    wceq
    wch
    wth
    @3
    vtocl3gf.6
    imbi2d
    wph
    wps
    vx
    cA
    cvv
    vtocl3gf.a
    vtocl3gf.1
    vtocl3gf.4
    vtocl3gf.7
    vtoclgf
    vtocl2gf
    mpan9
    3impb
end
