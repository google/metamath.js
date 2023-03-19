include "wfn.mm"
include "wss.mm"
include "cres.mm"
include "fnssres.mm"
include "syl2anc.mm"

theorem fnssresd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  assume fnssresd.1: |- ( ph -> F Fn A )
  assume fnssresd.2: |- ( ph -> B C_ A )


  assert |- ( ph -> ( F |` B ) Fn B )

  proof
    wph
    cF
    cA
    wfn
    cB
    cA
    wss
    cF
    cB
    cres
    cB
    wfn
    fnssresd.1
    fnssresd.2
    cA
    cB
    cF
    fnssres
    syl2anc
end
