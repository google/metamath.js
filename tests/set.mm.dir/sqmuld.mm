include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "sqmul.mm"
include "syl2anc.mm"

theorem sqmuld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume expcld.1: |- ( ph -> A e. CC )
  assume mulexpd.2: |- ( ph -> B e. CC )


  assert |- ( ph -> ( ( A x. B ) ^ 2 ) = ( ( A ^ 2 ) x. ( B ^ 2 ) ) )

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
    cmul
    co
    c2
    cexp
    co
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    cmul
    co
    wceq
    expcld.1
    mulexpd.2
    cA
    cB
    sqmul
    syl2anc
end
