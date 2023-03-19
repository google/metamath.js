include "ccncf.mm"
include "co.mm"
include "ccn.mm"
include "wcel.mm"
include "wf.mm"
include "fmpti.mm"
include "cc.mm"
include "wss.mm"
include "wb.mm"
include "cmpt.mm"
include "cres.mm"
include "wceq.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtr4i.mm"
include "eqeltrri.mm"
include "rescncf.mm"
include "mp2.mm"
include "eqeltri.mm"
include "cncffvrn.mm"
include "mp2an.mm"
include "mpbir.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "eqid.mm"
include "cncfmet.mm"
include "eleqtri.mm"

theorem cncfres
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  assume cncfres.1: |- A C_ CC
  assume cncfres.2: |- B C_ CC
  assume cncfres.3: |- F = ( x e. CC |-> C )
  assume cncfres.4: |- G = ( x e. A |-> C )
  assume cncfres.5: |- ( x e. A -> C e. B )
  assume cncfres.6: |- F e. ( CC -cn-> CC )
  assume cncfres.7: |- J = ( MetOpen ` ( ( abs o. - ) |` ( A X. A ) ) )
  assume cncfres.8: |- K = ( MetOpen ` ( ( abs o. - ) |` ( B X. B ) ) )

  disjoint A x
  disjoint B x
  disjoint J x
  disjoint K x
  assert |- G e. ( J Cn K )

  proof
    cG
    cA
    cB
    ccncf
    co
    #
    cJ
    cK
    ccn
    co
    #
    cG
    @0
    wcel
    #
    cA
    cB
    cG
    wf
    #
    vx
    cA
    cB
    cC
    cG
    cncfres.4
    cncfres.5
    fmpti
    cB
    cc
    wss
    #
    cG
    cA
    cc
    ccncf
    co
    #
    wcel
    @2
    @3
    wb
    cncfres.2
    cG
    vx
    cc
    cC
    cmpt
    #
    cA
    cres
    #
    @5
    cG
    vx
    cA
    cC
    cmpt
    #
    @7
    cncfres.4
    cA
    cc
    wss
    #
    @7
    @8
    wceq
    cncfres.1
    vx
    cc
    cA
    cC
    resmpt
    ax-mp
    eqtr4i
    @9
    @6
    cc
    cc
    ccncf
    co
    #
    wcel
    @7
    @5
    wcel
    cncfres.1
    cF
    @6
    @10
    cncfres.3
    cncfres.6
    eqeltrri
    cc
    cc
    cA
    @6
    rescncf
    mp2
    eqeltri
    cA
    cc
    cB
    cG
    cncffvrn
    mp2an
    mpbir
    @9
    @4
    @0
    @1
    wceq
    cncfres.1
    cncfres.2
    cA
    cB
    cabs
    cmin
    ccom
    #
    cA
    cA
    cxp
    cres
    #
    @11
    cB
    cB
    cxp
    cres
    #
    cJ
    cK
    @12
    eqid
    @13
    eqid
    cncfres.7
    cncfres.8
    cncfmet
    mp2an
    eleqtri
end
