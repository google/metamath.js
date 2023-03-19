include "cxr.mm"
include "wss.mm"
include "clt.mm"
include "csup.mm"
include "wcel.mm"
include "supxrcl.mm"
include "syl.mm"

theorem supxrcld
  let wph: wff ph
  let cA: class A
  assume supxrcld.1: |- ( ph -> A C_ RR* )


  assert |- ( ph -> sup ( A , RR* , < ) e. RR* )

  proof
    wph
    cA
    cxr
    wss
    cA
    cxr
    clt
    csup
    cxr
    wcel
    supxrcld.1
    cA
    supxrcl
    syl
end
