include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cv.mm"
include "copab.mm"
include "cfv.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "opelopabg.mm"
include "wb.mm"
include "wfn.mm"
include "fnopab.mm"
include "fnopfvb.mm"
include "mpan.mm"
include "eleq2i.mm"
include "syl6bb.mm"
include "adantr.mm"
include "ibar.mm"
include "3bitr4d.mm"

theorem fvopab3g
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  assume fvopab3g.2: |- ( x = A -> ( ph <-> ps ) )
  assume fvopab3g.3: |- ( y = B -> ( ps <-> ch ) )
  assume fvopab3g.4: |- ( x e. C -> E! y ph )
  assume fvopab3g.5: |- F = { <. x , y >. | ( x e. C /\ ph ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ch x
  disjoint ch y
  assert |- ( ( A e. C /\ B e. D ) -> ( ( F ` A ) = B <-> ch ) )

  proof
    cA
    cC
    wcel
    #
    cB
    cD
    wcel
    #
    wa
    cA
    cB
    cop
    #
    vx
    cv
    #
    cC
    wcel
    #
    wph
    wa
    #
    vx
    vy
    copab
    #
    wcel
    #
    @0
    wch
    wa
    #
    cA
    cF
    cfv
    cB
    wceq
    #
    wch
    @5
    @0
    wps
    wa
    @8
    vx
    vy
    cA
    cB
    cC
    cD
    @3
    cA
    wceq
    @4
    @0
    wph
    wps
    @3
    cA
    cC
    eleq1
    fvopab3g.2
    anbi12d
    vy
    cv
    cB
    wceq
    wps
    wch
    @0
    fvopab3g.3
    anbi2d
    opelopabg
    @0
    @9
    @7
    wb
    @1
    @0
    @9
    @2
    cF
    wcel
    #
    @7
    cF
    cC
    wfn
    @0
    @9
    @10
    wb
    wph
    vx
    vy
    cC
    cF
    fvopab3g.4
    fvopab3g.5
    fnopab
    cC
    cA
    cB
    cF
    fnopfvb
    mpan
    cF
    @6
    @2
    fvopab3g.5
    eleq2i
    syl6bb
    adantr
    @0
    wch
    @8
    wb
    @1
    @0
    wch
    ibar
    adantr
    3bitr4d
end
