include "cxr.mm"
include "wss.mm"
include "clt.mm"
include "cinf.mm"
include "wcel.mm"
include "infxrcl.mm"
include "syl.mm"

theorem infxrcld
  let wph: wff ph
  let cA: class A
  assume infxrcld.1: |- ( ph -> A C_ RR* )


  assert |- ( ph -> inf ( A , RR* , < ) e. RR* )

  proof
    wph
    cA
    cxr
    wss
    cA
    cxr
    clt
    cinf
    cxr
    wcel
    infxrcld.1
    cA
    infxrcl
    syl
end
