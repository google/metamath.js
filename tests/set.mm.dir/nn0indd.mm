include "cn0.mm"
include "wcel.mm"
include "wi.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "imbi2d.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wa.mm"
include "ex.mm"
include "expcom.mm"
include "a2d.mm"
include "nn0ind.mm"
include "impcom.mm"

theorem nn0indd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume nn0indd.1: |- ( x = 0 -> ( ps <-> ch ) )
  assume nn0indd.2: |- ( x = y -> ( ps <-> th ) )
  assume nn0indd.3: |- ( x = ( y + 1 ) -> ( ps <-> ta ) )
  assume nn0indd.4: |- ( x = A -> ( ps <-> et ) )
  assume nn0indd.5: |- ( ph -> ch )
  assume nn0indd.6: |- ( ( ( ph /\ y e. NN0 ) /\ th ) -> ta )

  disjoint A x
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint ps y
  disjoint ch x
  disjoint et x
  disjoint th x
  disjoint ta x
  assert |- ( ( ph /\ A e. NN0 ) -> et )

  proof
    cA
    cn0
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
    cc0
    wceq
    wps
    wch
    wph
    nn0indd.1
    imbi2d
    @0
    vy
    cv
    #
    wceq
    wps
    wth
    wph
    nn0indd.2
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
    nn0indd.3
    imbi2d
    @0
    cA
    wceq
    wps
    wet
    wph
    nn0indd.4
    imbi2d
    nn0indd.5
    @1
    cn0
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
    nn0indd.6
    ex
    expcom
    a2d
    nn0ind
    impcom
end
