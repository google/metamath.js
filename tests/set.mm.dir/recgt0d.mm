include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "recgt0.mm"
include "syl2anc.mm"

theorem recgt0d
  let wph: wff ph
  let cA: class A
  assume ltp1d.1: |- ( ph -> A e. RR )
  assume recgt0d.2: |- ( ph -> 0 < A )


  assert |- ( ph -> 0 < ( 1 / A ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    clt
    wbr
    cc0
    c1
    cA
    cdiv
    co
    clt
    wbr
    ltp1d.1
    recgt0d.2
    cA
    recgt0
    syl2anc
end
