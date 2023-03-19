include "copab.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wrel.mm"
include "wceq.mm"
include "relopab.mm"
include "1st2nd.mm"
include "mpan.mm"
include "id.mm"
include "eqeltrrd.mm"
include "fvex.mm"
include "opelopab.mm"
include "sylib.mm"

theorem elopabi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume elopabi.1: |- ( x = ( 1st ` A ) -> ( ph <-> ps ) )
  assume elopabi.2: |- ( y = ( 2nd ` A ) -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ch x
  disjoint ch y
  assert |- ( A e. { <. x , y >. | ph } -> ch )

  proof
    cA
    wph
    vx
    vy
    copab
    #
    wcel
    #
    cA
    c1st
    cfv
    #
    cA
    c2nd
    cfv
    #
    cop
    #
    @0
    wcel
    wch
    @1
    cA
    @4
    @0
    @0
    wrel
    @1
    cA
    @4
    wceq
    wph
    vx
    vy
    relopab
    cA
    @0
    1st2nd
    mpan
    @1
    id
    eqeltrrd
    wph
    wps
    wch
    vx
    vy
    @2
    @3
    cA
    c1st
    fvex
    cA
    c2nd
    fvex
    elopabi.1
    elopabi.2
    opelopab
    sylib
end
