include "crp.mm"
include "wcel.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "rphalflt.mm"
include "syl.mm"

theorem rphalfltd
  let wph: wff ph
  let cA: class A
  assume rphalfltd.1: |- ( ph -> A e. RR+ )


  assert |- ( ph -> ( A / 2 ) < A )

  proof
    wph
    cA
    crp
    wcel
    cA
    c2
    cdiv
    co
    cA
    clt
    wbr
    rphalfltd.1
    cA
    rphalflt
    syl
end
