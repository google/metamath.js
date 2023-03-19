include "nfcv.mm"
include "setrec2.mm"

theorem setrec2v
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let va: setvar a
  let vk: setvar k
  let vx: setvar x
  assume setrec2.b: |- B = setrecs ( F )
  assume setrec2.c: |- ( ph -> A. a ( a C_ C -> ( F ` a ) C_ C ) )

  disjoint F a
  disjoint C a
  disjoint k x
  assert |- ( ph -> B C_ C )

  proof
    wph
    cB
    cC
    cF
    va
    va
    cF
    nfcv
    setrec2.b
    setrec2.c
    setrec2
end
