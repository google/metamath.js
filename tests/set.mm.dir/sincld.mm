include "cc.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "sincl.mm"
include "syl.mm"

theorem sincld
  let wph: wff ph
  let cA: class A
  assume sincld.1: |- ( ph -> A e. CC )


  assert |- ( ph -> ( sin ` A ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cA
    csin
    cfv
    cc
    wcel
    sincld.1
    cA
    sincl
    syl
end
