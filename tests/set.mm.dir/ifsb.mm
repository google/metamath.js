include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "syl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61i.mm"

theorem ifsb
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  assume ifsb.1: |- ( if ( ph , A , B ) = A -> C = D )
  assume ifsb.2: |- ( if ( ph , A , B ) = B -> C = E )


  assert |- C = if ( ph , D , E )

  proof
    wph
    cC
    wph
    cD
    cE
    cif
    #
    wceq
    wph
    cC
    cD
    @0
    wph
    wph
    cA
    cB
    cif
    #
    cA
    wceq
    cC
    cD
    wceq
    wph
    cA
    cB
    iftrue
    ifsb.1
    syl
    wph
    cD
    cE
    iftrue
    eqtr4d
    wph
    wn
    #
    cC
    cE
    @0
    @2
    @1
    cB
    wceq
    cC
    cE
    wceq
    wph
    cA
    cB
    iffalse
    ifsb.2
    syl
    wph
    cD
    cE
    iffalse
    eqtr4d
    pm2.61i
end
