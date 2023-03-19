include "wcel.mm"
include "csn.mm"
include "wral.mm"
include "cv.mm"
include "wceq.mm"
include "ralbidv.mm"
include "ralsng.mm"
include "sylan9bb.mm"

theorem 2ralsng
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cW: class W
  assume ralsng.1: |- ( x = A -> ( ph <-> ps ) )
  assume 2ralsng.1: |- ( y = B -> ( ps <-> ch ) )

  disjoint A x
  disjoint ps x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint ch y
  assert |- ( ( A e. V /\ B e. W ) -> ( A. x e. { A } A. y e. { B } ph <-> ch ) )

  proof
    cA
    cV
    wcel
    wph
    vy
    cB
    csn
    #
    wral
    #
    vx
    cA
    csn
    wral
    wps
    vy
    @0
    wral
    #
    cB
    cW
    wcel
    wch
    @1
    @2
    vx
    cA
    cV
    vx
    cv
    cA
    wceq
    wph
    wps
    vy
    @0
    ralsng.1
    ralbidv
    ralsng
    wps
    wch
    vy
    cB
    cW
    2ralsng.1
    ralsng
    sylan9bb
end
