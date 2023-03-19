include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "elnnuz.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "wral.mm"
include "wi.mm"
include "sylbir.mm"
include "uzsinds.mm"
include "sylbi.mm"

theorem nnsinds
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume nnsinds.1: |- ( x = y -> ( ph <-> ps ) )
  assume nnsinds.2: |- ( x = N -> ( ph <-> ch ) )
  assume nnsinds.3: |- ( x e. NN -> ( A. y e. ( 1 ... ( x - 1 ) ) ps -> ph ) )

  disjoint ch x
  disjoint N x
  disjoint ph y
  disjoint ps x
  disjoint x y
  assert |- ( N e. NN -> ch )

  proof
    cN
    cn
    wcel
    cN
    c1
    cuz
    cfv
    #
    wcel
    wch
    cN
    elnnuz
    wph
    wps
    wch
    vx
    vy
    c1
    cN
    nnsinds.1
    nnsinds.2
    vx
    cv
    #
    @0
    wcel
    @1
    cn
    wcel
    wps
    vy
    c1
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
    elnnuz
    nnsinds.3
    sylbir
    uzsinds
    sylbi
end
