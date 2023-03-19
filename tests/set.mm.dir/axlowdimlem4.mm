include "c1.mm"
include "c2.mm"
include "cfz.mm"
include "co.mm"
include "cpr.mm"
include "cop.mm"
include "wf.mm"
include "cr.mm"
include "wss.mm"
include "wne.mm"
include "1ne2.mm"
include "1ex.mm"
include "2ex.mm"
include "elexi.mm"
include "fpr.mm"
include "ax-mp.mm"
include "caddc.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "1z.mm"
include "fzpr.mm"
include "df-2.mm"
include "oveq2i.mm"
include "preq2i.mm"
include "3eqtr4i.mm"
include "feq2i.mm"
include "mpbir.mm"
include "wa.mm"
include "pm3.2i.mm"
include "prss.mm"
include "mpbi.mm"
include "fss.mm"
include "mp2an.mm"

theorem axlowdimlem4
  let cA: class A
  let cB: class B
  assume axlowdimlem4.1: |- A e. RR
  assume axlowdimlem4.2: |- B e. RR


  assert |- { <. 1 , A >. , <. 2 , B >. } : ( 1 ... 2 ) --> RR

  proof
    c1
    c2
    cfz
    co
    #
    cA
    cB
    cpr
    #
    c1
    cA
    cop
    c2
    cB
    cop
    cpr
    #
    wf
    #
    @1
    cr
    wss
    #
    @0
    cr
    @2
    wf
    @3
    c1
    c2
    cpr
    #
    @1
    @2
    wf
    #
    c1
    c2
    wne
    @6
    1ne2
    c1
    c2
    cA
    cB
    1ex
    2ex
    cA
    cr
    axlowdimlem4.1
    elexi
    #
    cB
    cr
    axlowdimlem4.2
    elexi
    #
    fpr
    ax-mp
    @0
    @5
    @1
    @2
    c1
    c1
    c1
    caddc
    co
    #
    cfz
    co
    #
    c1
    @9
    cpr
    #
    @0
    @5
    c1
    cz
    wcel
    @10
    @11
    wceq
    1z
    c1
    fzpr
    ax-mp
    c2
    @9
    c1
    cfz
    df-2
    oveq2i
    c2
    @9
    c1
    df-2
    preq2i
    3eqtr4i
    feq2i
    mpbir
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    @4
    @12
    @13
    axlowdimlem4.1
    axlowdimlem4.2
    pm3.2i
    cA
    cB
    cr
    @7
    @8
    prss
    mpbi
    @0
    @1
    cr
    @2
    fss
    mp2an
end
