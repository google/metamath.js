include "csn.mm"
include "cun.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "ralunb.mm"
include "ralsng.mm"
include "anbi2d.mm"
include "syl5bb.mm"

theorem ralunsn
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  assume ralunsn.1: |- ( x = B -> ( ph <-> ps ) )

  disjoint B x
  disjoint ps x
  assert |- ( B e. C -> ( A. x e. ( A u. { B } ) ph <-> ( A. x e. A ph /\ ps ) ) )

  proof
    wph
    vx
    cA
    cB
    csn
    #
    cun
    wral
    wph
    vx
    cA
    wral
    #
    wph
    vx
    @0
    wral
    #
    wa
    cB
    cC
    wcel
    #
    @1
    wps
    wa
    wph
    vx
    cA
    @0
    ralunb
    @3
    @2
    wps
    @1
    wph
    wps
    vx
    cB
    cC
    ralunsn.1
    ralsng
    anbi2d
    syl5bb
end
