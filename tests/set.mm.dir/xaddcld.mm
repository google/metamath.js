include "cxr.mm"
include "wcel.mm"
include "cxad.mm"
include "co.mm"
include "xaddcl.mm"
include "syl2anc.mm"

theorem xaddcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume xnegcld.1: |- ( ph -> A e. RR* )
  assume xaddcld.2: |- ( ph -> B e. RR* )


  assert |- ( ph -> ( A +e B ) e. RR* )

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
    cxr
    wcel
    xnegcld.1
    xaddcld.2
    cA
    cB
    xaddcl
    syl2anc
end
