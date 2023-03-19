include "cop.mm"
include "copab.mm"
include "wcel.mm"
include "wsbc.mm"
include "opelopabsb.mm"
include "cvv.mm"
include "wb.mm"
include "nfcv.mm"
include "nfsbc.mm"
include "cv.mm"
include "wceq.mm"
include "sbcbidv.mm"
include "sbciegf.mm"
include "ax-mp.mm"
include "3bitri.mm"

theorem opelopabf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  assume opelopabf.x: |- F/ x ps
  assume opelopabf.y: |- F/ y ch
  assume opelopabf.1: |- A e. _V
  assume opelopabf.2: |- B e. _V
  assume opelopabf.3: |- ( x = A -> ( ph <-> ps ) )
  assume opelopabf.4: |- ( y = B -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( <. A , B >. e. { <. x , y >. | ph } <-> ch )

  proof
    cA
    cB
    cop
    wph
    vx
    vy
    copab
    wcel
    wph
    vy
    cB
    wsbc
    #
    vx
    cA
    wsbc
    #
    wps
    vy
    cB
    wsbc
    #
    wch
    wph
    vx
    vy
    cA
    cB
    opelopabsb
    cA
    cvv
    wcel
    @1
    @2
    wb
    opelopabf.1
    @0
    @2
    vx
    cA
    cvv
    wps
    vx
    vy
    cB
    vx
    cB
    nfcv
    opelopabf.x
    nfsbc
    vx
    cv
    cA
    wceq
    wph
    wps
    vy
    cB
    opelopabf.3
    sbcbidv
    sbciegf
    ax-mp
    cB
    cvv
    wcel
    @2
    wch
    wb
    opelopabf.2
    wps
    wch
    vy
    cB
    cvv
    opelopabf.y
    opelopabf.4
    sbciegf
    ax-mp
    3bitri
end
