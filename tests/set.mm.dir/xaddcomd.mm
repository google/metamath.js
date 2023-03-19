include "cxr.mm"
include "wcel.mm"
include "cxad.mm"
include "co.mm"
include "wceq.mm"
include "xaddcom.mm"
include "syl2anc.mm"

theorem xaddcomd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xaddcomd.1: |- ( ph -> A e. RR* )
  assume xaddcomd.2: |- ( ph -> B e. RR* )


  assert |- ( ph -> ( A +e B ) = ( B +e A ) )

  proof
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cxad
    co
    cB
    cA
    cxad
    co
    wceq
    xaddcomd.1
    xaddcomd.2
    cA
    cB
    xaddcom
    syl2anc
end
