include "cn.mm"
include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "c1.mm"
include "wceq.mm"
include "imbi2d.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nnind.mm"
include "impcom.mm"

theorem nnindd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nnindd.1: |- ( x = 1 -> ( ps <-> ch ) )
  assume nnindd.2: |- ( x = y -> ( ps <-> th ) )
  assume nnindd.3: |- ( x = ( y + 1 ) -> ( ps <-> ta ) )
  assume nnindd.4: |- ( x = A -> ( ps <-> et ) )
  assume nnindd.5: |- ( ph -> ch )
  assume nnindd.6: |- ( ( ( ph /\ y e. NN ) /\ th ) -> ta )

  disjoint A x
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint ch x
  disjoint et x
  disjoint th x
  disjoint ta x
  assert |- ( ( ph /\ A e. NN ) -> et )

  proof
    cA
    cn
    wcel
    wph
    wet
    wph
    wps
    wi
    wph
    wch
    wi
    wph
    wth
    wi
    wph
    wta
    wi
    wph
    wet
    wi
    vx
    vy
    cA
    vx
    cv
    #
    c1
    wceq
    wps
    wch
    wph
    nnindd.1
    imbi2d
    @0
    vy
    cv
    #
    wceq
    wps
    wth
    wph
    nnindd.2
    imbi2d
    @0
    @1
    c1
    caddc
    co
    wceq
    wps
    wta
    wph
    nnindd.3
    imbi2d
    @0
    cA
    wceq
    wps
    wet
    wph
    nnindd.4
    imbi2d
    nnindd.5
    @1
    cn
    wcel
    #
    wph
    wth
    wta
    wph
    @2
    wth
    wta
    wi
    wph
    @2
    wa
    wth
    wta
    nnindd.6
    ex
    expcom
    a2d
    nnind
    impcom
end
