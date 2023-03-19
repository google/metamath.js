include "wcel.mm"
include "cvv.mm"
include "elex.mm"
include "wi.mm"
include "nfel1.mm"
include "nfim.mm"
include "cv.mm"
include "wceq.mm"
include "imbi2d.mm"
include "vtoclgf.mm"
include "mpan9.mm"

theorem vtocl2gf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume vtocl2gf.1: |- F/_ x A
  assume vtocl2gf.2: |- F/_ y A
  assume vtocl2gf.3: |- F/_ y B
  assume vtocl2gf.4: |- F/ x ps
  assume vtocl2gf.5: |- F/ y ch
  assume vtocl2gf.6: |- ( x = A -> ( ph <-> ps ) )
  assume vtocl2gf.7: |- ( y = B -> ( ps <-> ch ) )
  assume vtocl2gf.8: |- ph


  assert |- ( ( A e. V /\ B e. W ) -> ch )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cB
    cW
    wcel
    wch
    cA
    cV
    elex
    @0
    wps
    wi
    @0
    wch
    wi
    vy
    cB
    cW
    vtocl2gf.3
    @0
    wch
    vy
    vy
    cA
    cvv
    vtocl2gf.2
    nfel1
    vtocl2gf.5
    nfim
    vy
    cv
    cB
    wceq
    wps
    wch
    @0
    vtocl2gf.7
    imbi2d
    wph
    wps
    vx
    cA
    cvv
    vtocl2gf.1
    vtocl2gf.4
    vtocl2gf.6
    vtocl2gf.8
    vtoclgf
    vtoclgf
    mpan9
end
