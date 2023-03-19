include "cif.mm"
include "co.mm"
include "wceq.mm"
include "iftrue.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "pm2.61i.mm"

theorem ovif12
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( if ( ph , A , B ) F if ( ph , C , D ) ) = if ( ph , ( A F C ) , ( B F D ) )

  proof
    wph
    wph
    cA
    cB
    cif
    #
    wph
    cC
    cD
    cif
    #
    cF
    co
    #
    wph
    cA
    cC
    cF
    co
    #
    cB
    cD
    cF
    co
    #
    cif
    #
    wceq
    wph
    @2
    @3
    @5
    wph
    @0
    cA
    @1
    cC
    cF
    wph
    cA
    cB
    iftrue
    wph
    cC
    cD
    iftrue
    oveq12d
    wph
    @3
    @4
    iftrue
    eqtr4d
    wph
    wn
    #
    @2
    @4
    @5
    @6
    @0
    cB
    @1
    cD
    cF
    wph
    cA
    cB
    iffalse
    wph
    cC
    cD
    iffalse
    oveq12d
    wph
    @3
    @4
    iffalse
    eqtr4d
    pm2.61i
end
