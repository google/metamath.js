include "crp.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "rpgt0.mm"
include "syl.mm"

theorem rpgt0d
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> 0 < A )

  proof
    wph
    cA
    crp
    wcel
    cc0
    cA
    clt
    wbr
    rpred.1
    cA
    rpgt0
    syl
end
