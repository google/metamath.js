include "crp.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "rpge0.mm"
include "syl.mm"

theorem rpge0d
  let wph: wff ph
  let cA: class A
  assume rpred.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> 0 <_ A )

  proof
    wph
    cA
    crp
    wcel
    cc0
    cA
    cle
    wbr
    rpred.1
    cA
    rpge0
    syl
end
