include "cv.mm"
include "cst.mm"
include "wcel.mm"
include "cin.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "caddc.mm"
include "co.mm"
include "c3.mm"
include "cort.mm"
include "chj.mm"
include "cch.mm"
include "choccli.mm"
include "chincli.mm"
include "chjcli.mm"
include "eqeltri.mm"
include "stm1add3i.mm"
include "golem1.mm"
include "eqeq1d.mm"
include "sylibd.mm"
include "stadd3i.mm"
include "syld.mm"

theorem golem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  assume golem1.1: |- A e. CH
  assume golem1.2: |- B e. CH
  assume golem1.3: |- C e. CH
  assume golem1.4: |- F = ( ( _|_ ` A ) vH ( A i^i B ) )
  assume golem1.5: |- G = ( ( _|_ ` B ) vH ( B i^i C ) )
  assume golem1.6: |- H = ( ( _|_ ` C ) vH ( C i^i A ) )
  assume golem1.7: |- D = ( ( _|_ ` B ) vH ( B i^i A ) )
  assume golem1.8: |- R = ( ( _|_ ` C ) vH ( C i^i B ) )
  assume golem1.9: |- S = ( ( _|_ ` A ) vH ( A i^i C ) )


  assert |- ( f e. States -> ( ( f ` ( ( F i^i G ) i^i H ) ) = 1 -> ( f ` D ) = 1 ) )

  proof
    vf
    cv
    #
    cst
    wcel
    #
    cF
    cG
    cin
    cH
    cin
    @0
    cfv
    c1
    wceq
    #
    cD
    @0
    cfv
    #
    cR
    @0
    cfv
    caddc
    co
    cS
    @0
    cfv
    caddc
    co
    #
    c3
    wceq
    #
    @3
    c1
    wceq
    @1
    @2
    cF
    @0
    cfv
    cG
    @0
    cfv
    caddc
    co
    cH
    @0
    cfv
    caddc
    co
    #
    c3
    wceq
    @5
    cF
    cG
    cH
    @0
    cF
    cA
    cort
    cfv
    #
    cA
    cB
    cin
    #
    chj
    co
    cch
    golem1.4
    @7
    @8
    cA
    golem1.1
    choccli
    #
    cA
    cB
    golem1.1
    golem1.2
    chincli
    chjcli
    eqeltri
    cG
    cB
    cort
    cfv
    #
    cB
    cC
    cin
    #
    chj
    co
    cch
    golem1.5
    @10
    @11
    cB
    golem1.2
    choccli
    #
    cB
    cC
    golem1.2
    golem1.3
    chincli
    chjcli
    eqeltri
    cH
    cC
    cort
    cfv
    #
    cC
    cA
    cin
    #
    chj
    co
    cch
    golem1.6
    @13
    @14
    cC
    golem1.3
    choccli
    #
    cC
    cA
    golem1.3
    golem1.1
    chincli
    chjcli
    eqeltri
    stm1add3i
    @1
    @6
    @4
    c3
    cA
    cB
    cC
    cD
    cR
    cS
    vf
    cF
    cG
    cH
    golem1.1
    golem1.2
    golem1.3
    golem1.4
    golem1.5
    golem1.6
    golem1.7
    golem1.8
    golem1.9
    golem1
    eqeq1d
    sylibd
    cD
    cR
    cS
    @0
    cD
    @10
    cB
    cA
    cin
    #
    chj
    co
    cch
    golem1.7
    @10
    @16
    @12
    cB
    cA
    golem1.2
    golem1.1
    chincli
    chjcli
    eqeltri
    cR
    @13
    cC
    cB
    cin
    #
    chj
    co
    cch
    golem1.8
    @13
    @17
    @15
    cC
    cB
    golem1.3
    golem1.2
    chincli
    chjcli
    eqeltri
    cS
    @7
    cA
    cC
    cin
    #
    chj
    co
    cch
    golem1.9
    @7
    @18
    @9
    cA
    cC
    golem1.1
    golem1.3
    chincli
    chjcli
    eqeltri
    stadd3i
    syld
end
