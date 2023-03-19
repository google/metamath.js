include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "wral.mm"
include "wa.mm"
include "ralunsn.mm"
include "ralbidv.mm"
include "cv.mm"
include "wceq.mm"
include "anbi12d.mm"
include "r19.26.mm"
include "anbi1i.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem 2ralunsn
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  assume 2ralunsn.1: |- ( x = B -> ( ph <-> ch ) )
  assume 2ralunsn.2: |- ( y = B -> ( ph <-> ps ) )
  assume 2ralunsn.3: |- ( x = B -> ( ps <-> th ) )

  disjoint A x
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint C x
  disjoint ch x
  disjoint ps y
  disjoint th x
  assert |- ( B e. C -> ( A. x e. ( A u. { B } ) A. y e. ( A u. { B } ) ph <-> ( ( A. x e. A A. y e. A ph /\ A. x e. A ps ) /\ ( A. y e. A ch /\ th ) ) ) )

  proof
    cB
    cC
    wcel
    #
    wph
    vy
    cA
    cB
    csn
    cun
    #
    wral
    #
    vx
    @1
    wral
    wph
    vy
    cA
    wral
    #
    wps
    wa
    #
    vx
    @1
    wral
    #
    @3
    vx
    cA
    wral
    wps
    vx
    cA
    wral
    wa
    #
    wch
    vy
    cA
    wral
    #
    wth
    wa
    #
    wa
    #
    @0
    @2
    @4
    vx
    @1
    wph
    wps
    vy
    cA
    cB
    cC
    2ralunsn.2
    ralunsn
    ralbidv
    @0
    @5
    @4
    vx
    cA
    wral
    #
    @8
    wa
    @9
    @4
    @8
    vx
    cA
    cB
    cC
    vx
    cv
    cB
    wceq
    #
    @3
    @7
    wps
    wth
    @11
    wph
    wch
    vy
    cA
    2ralunsn.1
    ralbidv
    2ralunsn.3
    anbi12d
    ralunsn
    @10
    @6
    @8
    @3
    wps
    vx
    cA
    r19.26
    anbi1i
    syl6bb
    bitrd
end
