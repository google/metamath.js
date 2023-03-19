include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cabs.mm"
include "cfv.mm"
include "crp.mm"
include "absrpcl.mm"
include "syl2anc.mm"

theorem absrpcld
  let wph: wff ph
  let cA: class A
  assume abscld.1: |- ( ph -> A e. CC )
  assume absne0d.2: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( abs ` A ) e. RR+ )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cA
    cabs
    cfv
    crp
    wcel
    abscld.1
    absne0d.2
    cA
    absrpcl
    syl2anc
end
