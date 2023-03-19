include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "wb.mm"
include "elmapg.mm"
include "syl2anc.mm"

theorem elmapd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  assume elmapd.a: |- ( ph -> A e. V )
  assume elmapd.b: |- ( ph -> B e. W )


  assert |- ( ph -> ( C e. ( A ^m B ) <-> C : B --> A ) )

  proof
    wph
    cA
    cV
    wcel
    cB
    cW
    wcel
    cC
    cA
    cB
    cmap
    co
    wcel
    cB
    cA
    cC
    wf
    wb
    elmapd.a
    elmapd.b
    cA
    cB
    cC
    cV
    cW
    elmapg
    syl2anc
end
