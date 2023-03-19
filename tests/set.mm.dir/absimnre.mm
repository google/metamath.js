include "cim.mm"
include "cfv.mm"
include "imcld.mm"
include "recnd.mm"
include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "cc.mm"
include "wb.mm"
include "reim0b.mm"
include "syl.mm"
include "mtbid.mm"
include "neqned.mm"
include "absrpcld.mm"

theorem absimnre
  let wph: wff ph
  let cA: class A
  assume absimnre.1: |- ( ph -> A e. CC )
  assume absimnre.2: |- ( ph -> -. A e. RR )


  assert |- ( ph -> ( abs ` ( Im ` A ) ) e. RR+ )

  proof
    wph
    cA
    cim
    cfv
    #
    wph
    @0
    wph
    cA
    absimnre.1
    imcld
    recnd
    wph
    @0
    cc0
    wph
    cA
    cr
    wcel
    #
    @0
    cc0
    wceq
    #
    absimnre.2
    wph
    cA
    cc
    wcel
    @1
    @2
    wb
    absimnre.1
    cA
    reim0b
    syl
    mtbid
    neqned
    absrpcld
end
