include "wcel.mm"
include "cop.mm"
include "copab.mm"
include "cvv.mm"
include "wa.mm"
include "cxp.mm"
include "elopaelxp.mm"
include "opelxp1.mm"
include "syl.mm"
include "anim1i.mm"
include "ancoms.mm"
include "elex.mm"
include "opelopabg.mm"
include "pm5.21nd.mm"

theorem opelopab3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume opelopab3.1: |- ( x = A -> ( ph <-> ps ) )
  assume opelopab3.2: |- ( y = B -> ( ps <-> ch ) )
  assume opelopab3.3: |- ( ch -> A e. C )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ch x
  disjoint ch y
  assert |- ( B e. D -> ( <. A , B >. e. { <. x , y >. | ph } <-> ch ) )

  proof
    cB
    cD
    wcel
    #
    cA
    cB
    cop
    #
    wph
    vx
    vy
    copab
    wcel
    #
    wch
    cA
    cvv
    wcel
    #
    @0
    wa
    #
    @2
    @0
    @4
    @2
    @3
    @0
    @2
    @1
    cvv
    cvv
    cxp
    wcel
    @3
    wph
    vx
    vy
    @1
    elopaelxp
    cA
    cB
    cvv
    cvv
    opelxp1
    syl
    anim1i
    ancoms
    wch
    @0
    @4
    wch
    @3
    @0
    wch
    cA
    cC
    wcel
    @3
    opelopab3.3
    cA
    cC
    elex
    syl
    anim1i
    ancoms
    wph
    wps
    wch
    vx
    vy
    cA
    cB
    cvv
    cD
    opelopab3.1
    opelopab3.2
    opelopabg
    pm5.21nd
end
