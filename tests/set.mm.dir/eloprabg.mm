include "cv.mm"
include "wceq.mm"
include "syl3an9b.mm"
include "eloprabga.mm"

theorem eloprabg
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  let cX: class X
  assume eloprabg.1: |- ( x = A -> ( ph <-> ps ) )
  assume eloprabg.2: |- ( y = B -> ( ps <-> ch ) )
  assume eloprabg.3: |- ( z = C -> ( ch <-> th ) )

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint th x
  disjoint th y
  disjoint th z
  assert |- ( ( A e. V /\ B e. W /\ C e. X ) -> ( <. <. A , B >. , C >. e. { <. <. x , y >. , z >. | ph } <-> th ) )

  proof
    wph
    wth
    vx
    vy
    vz
    cA
    cB
    cC
    cV
    cW
    cX
    vx
    cv
    cA
    wceq
    wph
    wps
    vy
    cv
    cB
    wceq
    wch
    vz
    cv
    cC
    wceq
    wth
    eloprabg.1
    eloprabg.2
    eloprabg.3
    syl3an9b
    eloprabga
end
