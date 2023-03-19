include "wcel.mm"
include "wf.mm"
include "wss.mm"
include "cpm.mm"
include "co.mm"
include "elpm2r.mm"
include "syl22anc.mm"

theorem fpmd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V
  let cW: class W
  assume fpmd.a: |- ( ph -> A e. V )
  assume fpmd.b: |- ( ph -> B e. W )
  assume fpmd.c: |- ( ph -> C C_ A )
  assume fpmd.f: |- ( ph -> F : C --> B )


  assert |- ( ph -> F e. ( B ^pm A ) )

  proof
    wph
    cB
    cW
    wcel
    cA
    cV
    wcel
    cC
    cB
    cF
    wf
    cC
    cA
    wss
    cF
    cB
    cA
    cpm
    co
    wcel
    fpmd.b
    fpmd.a
    fpmd.f
    fpmd.c
    cB
    cA
    cC
    cF
    cW
    cV
    elpm2r
    syl22anc
end
