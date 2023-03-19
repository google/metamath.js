include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "wi.mm"
include "wss.mm"
include "cst.mm"
include "cort.mm"
include "chj.mm"
include "co.mm"
include "cch.mm"
include "choccli.mm"
include "chincli.mm"
include "chjcli.mm"
include "eqeltri.mm"
include "stri.mm"
include "eqid.mm"
include "golem2.mm"
include "mprg.mm"

theorem goeqi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let cH: class H
  let vf: setvar f
  assume goeq.1: |- A e. CH
  assume goeq.2: |- B e. CH
  assume goeq.3: |- C e. CH
  assume goeq.4: |- F = ( ( _|_ ` A ) vH ( A i^i B ) )
  assume goeq.5: |- G = ( ( _|_ ` B ) vH ( B i^i C ) )
  assume goeq.6: |- H = ( ( _|_ ` C ) vH ( C i^i A ) )
  assume goeq.7: |- D = ( ( _|_ ` B ) vH ( B i^i A ) )


  assert |- ( ( F i^i G ) i^i H ) C_ D

  proof
    cF
    cG
    cin
    #
    cH
    cin
    #
    vf
    cv
    #
    cfv
    c1
    wceq
    cD
    @2
    cfv
    c1
    wceq
    wi
    @1
    cD
    wss
    vf
    cst
    @1
    cD
    vf
    @0
    cH
    cF
    cG
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
    goeq.4
    @3
    @4
    cA
    goeq.1
    choccli
    cA
    cB
    goeq.1
    goeq.2
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
    goeq.5
    @5
    @6
    cB
    goeq.2
    choccli
    #
    cB
    cC
    goeq.2
    goeq.3
    chincli
    chjcli
    eqeltri
    chincli
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
    goeq.6
    @8
    @9
    cC
    goeq.3
    choccli
    cC
    cA
    goeq.3
    goeq.1
    chincli
    chjcli
    eqeltri
    chincli
    cD
    @5
    cB
    cA
    cin
    #
    chj
    co
    cch
    goeq.7
    @5
    @10
    @7
    cB
    cA
    goeq.2
    goeq.1
    chincli
    chjcli
    eqeltri
    stri
    cA
    cB
    cC
    cD
    @8
    cC
    cB
    cin
    chj
    co
    #
    @3
    cA
    cC
    cin
    chj
    co
    #
    vf
    cF
    cG
    cH
    goeq.1
    goeq.2
    goeq.3
    goeq.4
    goeq.5
    goeq.6
    goeq.7
    @11
    eqid
    @12
    eqid
    golem2
    mprg
end
