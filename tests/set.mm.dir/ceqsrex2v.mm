include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "anass.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "bitri.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ceqsrexv.mm"
include "syl5bb.mm"
include "sylan9bb.mm"

theorem ceqsrex2v
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ceqsrex2v.1: |- ( x = A -> ( ph <-> ps ) )
  assume ceqsrex2v.2: |- ( y = B -> ( ps <-> ch ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint D x
  disjoint D y
  disjoint ps x
  disjoint ch y
  assert |- ( ( A e. C /\ B e. D ) -> ( E. x e. C E. y e. D ( ( x = A /\ y = B ) /\ ph ) <-> ch ) )

  proof
    cA
    cC
    wcel
    #
    vx
    cv
    cA
    wceq
    #
    vy
    cv
    cB
    wceq
    #
    wa
    wph
    wa
    #
    vy
    cD
    wrex
    #
    vx
    cC
    wrex
    #
    @2
    wps
    wa
    #
    vy
    cD
    wrex
    #
    cB
    cD
    wcel
    wch
    @5
    @1
    @2
    wph
    wa
    #
    vy
    cD
    wrex
    #
    wa
    #
    vx
    cC
    wrex
    @0
    @7
    @4
    @10
    vx
    cC
    @4
    @1
    @8
    wa
    #
    vy
    cD
    wrex
    @10
    @3
    @11
    vy
    cD
    @1
    @2
    wph
    anass
    rexbii
    @1
    @8
    vy
    cD
    r19.42v
    bitri
    rexbii
    @9
    @7
    vx
    cA
    cC
    @1
    @8
    @6
    vy
    cD
    @1
    wph
    wps
    @2
    ceqsrex2v.1
    anbi2d
    rexbidv
    ceqsrexv
    syl5bb
    wps
    wch
    vy
    cB
    cD
    ceqsrex2v.2
    ceqsrexv
    sylan9bb
end
