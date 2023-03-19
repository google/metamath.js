include "cfv.mm"
include "csp.mm"
include "co.mm"
include "cva.mm"
include "cmv.mm"
include "cmin.mm"
include "ci.mm"
include "csm.mm"
include "cmul.mm"
include "caddc.mm"
include "c4.mm"
include "cdiv.mm"
include "chil.mm"
include "wcel.mm"
include "lnopfi.mm"
include "ffvelrni.mm"
include "ax-mp.mm"
include "polid2i.mm"
include "wceq.mm"
include "lnopaddi.mm"
include "mp2an.mm"
include "oveq1i.mm"
include "lnopsubi.mm"
include "oveq12i.mm"
include "cc.mm"
include "ax-icn.mm"
include "lnopaddmuli.mm"
include "mp3an.mm"
include "lnopsubmuli.mm"
include "oveq2i.mm"
include "eqtr4i.mm"

theorem lnopeq0lem1
  let cA: class A
  let cB: class B
  let cT: class T
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume lnopeq0.1: |- T e. LinOp
  assume lnopeq0lem1.2: |- A e. ~H
  assume lnopeq0lem1.3: |- B e. ~H


  assert |- ( ( T ` A ) .ih B ) = ( ( ( ( ( T ` ( A +h B ) ) .ih ( A +h B ) ) - ( ( T ` ( A -h B ) ) .ih ( A -h B ) ) ) + ( _i x. ( ( ( T ` ( A +h ( _i .h B ) ) ) .ih ( A +h ( _i .h B ) ) ) - ( ( T ` ( A -h ( _i .h B ) ) ) .ih ( A -h ( _i .h B ) ) ) ) ) ) / 4 )

  proof
    cA
    cT
    cfv
    #
    cB
    csp
    co
    @0
    cB
    cT
    cfv
    #
    cva
    co
    #
    cA
    cB
    cva
    co
    #
    csp
    co
    #
    @0
    @1
    cmv
    co
    #
    cA
    cB
    cmv
    co
    #
    csp
    co
    #
    cmin
    co
    #
    ci
    @0
    ci
    @1
    csm
    co
    #
    cva
    co
    #
    cA
    ci
    cB
    csm
    co
    #
    cva
    co
    #
    csp
    co
    #
    @0
    @9
    cmv
    co
    #
    cA
    @11
    cmv
    co
    #
    csp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    @3
    cT
    cfv
    #
    @3
    csp
    co
    #
    @6
    cT
    cfv
    #
    @6
    csp
    co
    #
    cmin
    co
    #
    ci
    @12
    cT
    cfv
    #
    @12
    csp
    co
    #
    @15
    cT
    cfv
    #
    @15
    csp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    @0
    cB
    @1
    cA
    cA
    chil
    wcel
    #
    @0
    chil
    wcel
    lnopeq0lem1.2
    chil
    chil
    cA
    cT
    cT
    lnopeq0.1
    lnopfi
    #
    ffvelrni
    ax-mp
    lnopeq0lem1.3
    cB
    chil
    wcel
    #
    @1
    chil
    wcel
    lnopeq0lem1.3
    chil
    chil
    cB
    cT
    @33
    ffvelrni
    ax-mp
    lnopeq0lem1.2
    polid2i
    @31
    @19
    c4
    cdiv
    @24
    @8
    @30
    @18
    caddc
    @21
    @4
    @23
    @7
    cmin
    @20
    @2
    @3
    csp
    @32
    @34
    @20
    @2
    wceq
    lnopeq0lem1.2
    lnopeq0lem1.3
    cA
    cB
    cT
    lnopeq0.1
    lnopaddi
    mp2an
    oveq1i
    @22
    @5
    @6
    csp
    @32
    @34
    @22
    @5
    wceq
    lnopeq0lem1.2
    lnopeq0lem1.3
    cA
    cB
    cT
    lnopeq0.1
    lnopsubi
    mp2an
    oveq1i
    oveq12i
    @29
    @17
    ci
    cmul
    @26
    @13
    @28
    @16
    cmin
    @25
    @10
    @12
    csp
    ci
    cc
    wcel
    #
    @32
    @34
    @25
    @10
    wceq
    ax-icn
    lnopeq0lem1.2
    lnopeq0lem1.3
    ci
    cA
    cB
    cT
    lnopeq0.1
    lnopaddmuli
    mp3an
    oveq1i
    @27
    @14
    @15
    csp
    @35
    @32
    @34
    @27
    @14
    wceq
    ax-icn
    lnopeq0lem1.2
    lnopeq0lem1.3
    ci
    cA
    cB
    cT
    lnopeq0.1
    lnopsubmuli
    mp3an
    oveq1i
    oveq12i
    oveq2i
    oveq12i
    oveq1i
    eqtr4i
end
