include "cmul.mm"
include "co.mm"
include "mulcld.mm"
include "mulcomd.mm"
include "subeq0bd.mm"

theorem bj-subcom
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume bj-subcom.a: |- ( ph -> A e. CC )
  assume bj-subcom.b: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( A x. B ) - ( B x. A ) ) = 0 )

  proof
    wph
    cA
    cB
    cmul
    co
    cB
    cA
    cmul
    co
    wph
    cA
    cB
    bj-subcom.a
    bj-subcom.b
    mulcld
    wph
    cA
    cB
    bj-subcom.a
    bj-subcom.b
    mulcomd
    subeq0bd
end
