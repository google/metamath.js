include "cop.mm"
include "copab.mm"
include "wcel.mm"
include "wsbc.mm"
include "wa.mm"
include "opelopabsb.mm"
include "nfcv.mm"
include "nfsbc.mm"
include "cv.mm"
include "wceq.mm"
include "sbcbidv.mm"
include "sbciegf.mm"
include "sylan9bb.mm"
include "syl5bb.mm"

theorem opelopabgf
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume opelopabgf.x: |- F/ x ps
  assume opelopabgf.y: |- F/ y ch
  assume opelopabgf.1: |- ( x = A -> ( ph <-> ps ) )
  assume opelopabgf.2: |- ( y = B -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( A e. V /\ B e. W ) -> ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) )

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
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    wa
    wch
    wph
    vx
    vy
    cA
    cB
    opelopabsb
    @2
    @1
    wps
    vy
    cB
    wsbc
    #
    @3
    wch
    @0
    @4
    vx
    cA
    cV
    wps
    vx
    vy
    cB
    vx
    cB
    nfcv
    opelopabgf.x
    nfsbc
    vx
    cv
    cA
    wceq
    wph
    wps
    vy
    cB
    opelopabgf.1
    sbcbidv
    sbciegf
    wps
    wch
    vy
    cB
    cW
    opelopabgf.y
    opelopabgf.2
    sbciegf
    sylan9bb
    syl5bb
end
