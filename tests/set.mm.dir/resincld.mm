include "cr.mm"
include "wcel.mm"
include "csin.mm"
include "cfv.mm"
include "resincl.mm"
include "syl.mm"

theorem resincld
  let wph: wff ph
  let cA: class A
  assume resincld.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( sin ` A ) e. RR )

  proof
    wph
    cA
    cr
    wcel
    cA
    csin
    cfv
    cr
    wcel
    resincld.1
    cA
    resincl
    syl
end
