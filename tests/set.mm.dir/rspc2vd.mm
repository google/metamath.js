include "csb.mm"
include "wcel.mm"
include "wral.mm"
include "csbied.mm"
include "eleqtrrd.mm"
include "wi.mm"
include "nfcsb1v.mm"
include "nfv.mm"
include "nfral.mm"
include "cv.mm"
include "wceq.mm"
include "csbeq1a.mm"
include "raleqbidv.mm"
include "rspc.mm"
include "syl.mm"
include "rspcv.mm"
include "sylsyld.mm"

theorem rspc2vd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume rspc2vd.a: |- ( x = A -> ( th <-> ch ) )
  assume rspc2vd.b: |- ( y = B -> ( ch <-> ps ) )
  assume rspc2vd.c: |- ( ph -> A e. C )
  assume rspc2vd.d: |- ( ( ph /\ x = A ) -> D = E )
  assume rspc2vd.e: |- ( ph -> B e. E )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint C x
  disjoint D y
  disjoint E x
  disjoint ph x
  disjoint ch x
  disjoint ps y
  assert |- ( ph -> ( A. x e. C A. y e. D th -> ps ) )

  proof
    wph
    cB
    vx
    cA
    cD
    csb
    #
    wcel
    wth
    vy
    cD
    wral
    #
    vx
    cC
    wral
    #
    wch
    vy
    @0
    wral
    #
    wps
    wph
    cB
    cE
    @0
    rspc2vd.e
    wph
    vx
    cA
    cD
    cE
    cC
    rspc2vd.c
    rspc2vd.d
    csbied
    eleqtrrd
    wph
    cA
    cC
    wcel
    @2
    @3
    wi
    rspc2vd.c
    @1
    @3
    vx
    cA
    cC
    wch
    vx
    vy
    @0
    vx
    cA
    cD
    nfcsb1v
    wch
    vx
    nfv
    nfral
    vx
    cv
    cA
    wceq
    wth
    wch
    vy
    cD
    @0
    vx
    cA
    cD
    csbeq1a
    rspc2vd.a
    raleqbidv
    rspc
    syl
    wch
    wps
    vy
    cB
    @0
    rspc2vd.b
    rspcv
    sylsyld
end
