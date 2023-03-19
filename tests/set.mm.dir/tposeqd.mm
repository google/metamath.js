include "wceq.mm"
include "ctpos.mm"
include "tposeq.mm"
include "syl.mm"

theorem tposeqd
  let wph: wff ph
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  assume tposeqd.1: |- ( ph -> F = G )


  assert |- ( ph -> tpos F = tpos G )

  proof
    wph
    cF
    cG
    wceq
    cF
    ctpos
    cG
    ctpos
    wceq
    tposeqd.1
    cF
    cG
    tposeq
    syl
end
