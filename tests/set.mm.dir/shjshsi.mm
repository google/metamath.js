include "chj.mm"
include "co.mm"
include "cph.mm"
include "cort.mm"
include "cfv.mm"
include "cun.mm"
include "csh.mm"
include "wcel.mm"
include "wceq.mm"
include "shjval.mm"
include "mp2an.mm"
include "wss.mm"
include "shunssi.mm"
include "chil.mm"
include "shssii.mm"
include "unssi.mm"
include "shscli.mm"
include "occon2i.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "shsleji.mm"
include "wi.mm"
include "shjcli.mm"
include "chssii.mm"
include "occon.mm"
include "cch.mm"
include "occl.mm"
include "chsscon1i.mm"
include "mpbi.mm"
include "eqssi.mm"

theorem shjshsi
  let cA: class A
  let cB: class B
  assume shjshs.1: |- A e. SH
  assume shjshs.2: |- B e. SH


  assert |- ( A vH B ) = ( _|_ ` ( _|_ ` ( A +H B ) ) )

  proof
    cA
    cB
    chj
    co
    #
    cA
    cB
    cph
    co
    #
    cort
    cfv
    #
    cort
    cfv
    #
    @0
    cA
    cB
    cun
    #
    cort
    cfv
    cort
    cfv
    #
    @3
    cA
    csh
    wcel
    cB
    csh
    wcel
    @0
    @5
    wceq
    shjshs.1
    shjshs.2
    cA
    cB
    shjval
    mp2an
    @4
    @1
    wss
    @5
    @3
    wss
    cA
    cB
    shjshs.1
    shjshs.2
    shunssi
    @4
    @1
    cA
    cB
    chil
    cA
    shjshs.1
    shssii
    cB
    shjshs.2
    shssii
    unssi
    @1
    cA
    cB
    shjshs.1
    shjshs.2
    shscli
    shssii
    #
    occon2i
    ax-mp
    eqsstri
    @0
    cort
    cfv
    @2
    wss
    #
    @3
    @0
    wss
    @1
    @0
    wss
    #
    @7
    cA
    cB
    shjshs.1
    shjshs.2
    shsleji
    @1
    chil
    wss
    #
    @0
    chil
    wss
    @8
    @7
    wi
    @6
    @0
    cA
    cB
    shjshs.1
    shjshs.2
    shjcli
    #
    chssii
    @1
    @0
    occon
    mp2an
    ax-mp
    @0
    @2
    @10
    @9
    @2
    cch
    wcel
    @6
    @1
    occl
    ax-mp
    chsscon1i
    mpbi
    eqssi
end
