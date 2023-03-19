include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "subcl.mm"
include "syl2anc.mm"

theorem subcld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( A - B ) e. CC )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cA
    cB
    cmin
    co
    cc
    wcel
    negidd.1
    pncand.2
    cA
    cB
    subcl
    syl2anc
end
