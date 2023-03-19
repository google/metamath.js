include "cif.mm"
include "co.mm"
include "wcel.mm"
include "iftrue.mm"
include "oveq12d.mm"
include "3eltr4d.mm"
include "wn.mm"
include "iffalse.mm"
include "syl6eqel.mm"
include "eleqtrrd.mm"
include "pm2.61i.mm"

theorem elimdelov
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume elimdelov.1: |- ( ph -> C e. ( A F B ) )
  assume elimdelov.2: |- Z e. ( X F Y )


  assert |- if ( ph , C , Z ) e. ( if ( ph , A , X ) F if ( ph , B , Y ) )

  proof
    wph
    wph
    cC
    cZ
    cif
    #
    wph
    cA
    cX
    cif
    #
    wph
    cB
    cY
    cif
    #
    cF
    co
    #
    wcel
    wph
    cC
    cA
    cB
    cF
    co
    @0
    @3
    elimdelov.1
    wph
    cC
    cZ
    iftrue
    wph
    @1
    cA
    @2
    cB
    cF
    wph
    cA
    cX
    iftrue
    wph
    cB
    cY
    iftrue
    oveq12d
    3eltr4d
    wph
    wn
    #
    @0
    cX
    cY
    cF
    co
    #
    @3
    @4
    @0
    cZ
    @5
    wph
    cC
    cZ
    iffalse
    elimdelov.2
    syl6eqel
    @4
    @1
    cX
    @2
    cY
    cF
    wph
    cA
    cX
    iffalse
    wph
    cB
    cY
    iffalse
    oveq12d
    eleqtrrd
    pm2.61i
end
