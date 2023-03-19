include "cr.mm"
include "wcel.mm"
include "cim.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cc.mm"
include "wb.mm"
include "reim0b.mm"
include "syl.mm"
include "mpbird.mm"

theorem reim0bd
  let wph: wff ph
  let cA: class A
  assume recld.1: |- ( ph -> A e. CC )
  assume reim0bd.2: |- ( ph -> ( Im ` A ) = 0 )


  assert |- ( ph -> A e. RR )

  proof
    wph
    cA
    cr
    wcel
    #
    cA
    cim
    cfv
    cc0
    wceq
    #
    reim0bd.2
    wph
    cA
    cc
    wcel
    @0
    @1
    wb
    recld.1
    cA
    reim0b
    syl
    mpbird
end
