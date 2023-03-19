include "cn0.mm"
include "wcel.mm"
include "cc0.mm"
include "cuz.mm"
include "cfv.mm"
include "elnn0uz.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wral.mm"
include "wi.mm"
include "sylbir.mm"
include "uzsinds.mm"
include "sylbi.mm"

theorem nn0sinds
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume nn0sinds.1: |- ( x = y -> ( ph <-> ps ) )
  assume nn0sinds.2: |- ( x = N -> ( ph <-> ch ) )
  assume nn0sinds.3: |- ( x e. NN0 -> ( A. y e. ( 0 ... ( x - 1 ) ) ps -> ph ) )

  disjoint ch x
  disjoint N x
  disjoint ph y
  disjoint ps x
  disjoint x y
  assert |- ( N e. NN0 -> ch )

  proof
    cN
    cn0
    wcel
    cN
    cc0
    cuz
    cfv
    #
    wcel
    wch
    cN
    elnn0uz
    wph
    wps
    wch
    vx
    vy
    cc0
    cN
    nn0sinds.1
    nn0sinds.2
    vx
    cv
    #
    @0
    wcel
    @1
    cn0
    wcel
    wps
    vy
    cc0
    @1
    c1
    cmin
    co
    cfz
    co
    wral
    wph
    wi
    @1
    elnn0uz
    nn0sinds.3
    sylbir
    uzsinds
    sylbi
end
