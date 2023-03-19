include "cr.mm"
include "wcel.mm"
include "cmnf.mm"
include "clt.mm"
include "wbr.mm"
include "mnflt.mm"
include "syl.mm"

theorem mnfltd
  let wph: wff ph
  let cA: class A
  assume mnfltd.a: |- ( ph -> A e. RR )


  assert |- ( ph -> -oo < A )

  proof
    wph
    cA
    cr
    wcel
    cmnf
    cA
    clt
    wbr
    mnfltd.a
    cA
    mnflt
    syl
end
