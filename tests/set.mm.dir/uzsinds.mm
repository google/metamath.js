include "cuz.mm"
include "cfv.mm"
include "clt.mm"
include "ltweuz.mm"
include "cvv.mm"
include "wcel.mm"
include "wse.mm"
include "fvex.mm"
include "exse.mm"
include "ax-mp.mm"
include "cv.mm"
include "cpred.mm"
include "wral.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "preduz.mm"
include "raleqdv.mm"
include "sylbid.mm"
include "wfis3.mm"

theorem uzsinds
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cM: class M
  let cN: class N
  assume uzsinds.1: |- ( x = y -> ( ph <-> ps ) )
  assume uzsinds.2: |- ( x = N -> ( ph <-> ch ) )
  assume uzsinds.3: |- ( x e. ( ZZ>= ` M ) -> ( A. y e. ( M ... ( x - 1 ) ) ps -> ph ) )

  disjoint ch x
  disjoint M x
  disjoint M y
  disjoint x y
  disjoint N x
  disjoint ph y
  disjoint ps x
  assert |- ( N e. ( ZZ>= ` M ) -> ch )

  proof
    wph
    wps
    wch
    vx
    vy
    cM
    cuz
    cfv
    #
    cN
    clt
    cM
    ltweuz
    @0
    cvv
    wcel
    @0
    clt
    wse
    cM
    cuz
    fvex
    @0
    clt
    cvv
    exse
    ax-mp
    uzsinds.1
    uzsinds.2
    vx
    cv
    #
    @0
    wcel
    #
    wps
    vy
    @0
    clt
    @1
    cpred
    #
    wral
    wps
    vy
    cM
    @1
    c1
    cmin
    co
    cfz
    co
    #
    wral
    wph
    @2
    wps
    vy
    @3
    @4
    cM
    @1
    preduz
    raleqdv
    uzsinds.3
    sylbid
    wfis3
end
