include "wcel.mm"
include "cxp.mm"
include "cres.mm"
include "co.mm"
include "wceq.mm"
include "ovres.mm"
include "syl2anc.mm"

theorem ovresd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cX: class X
  assume ovresd.1: |- ( ph -> A e. X )
  assume ovresd.2: |- ( ph -> B e. X )


  assert |- ( ph -> ( A ( D |` ( X X. X ) ) B ) = ( A D B ) )

  proof
    wph
    cA
    cX
    wcel
    cB
    cX
    wcel
    cA
    cB
    cD
    cX
    cX
    cxp
    cres
    co
    cA
    cB
    cD
    co
    wceq
    ovresd.1
    ovresd.2
    cA
    cB
    cX
    cX
    cD
    ovres
    syl2anc
end
