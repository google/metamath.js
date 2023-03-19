include "cph.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "wss.mm"
include "csh.mm"
include "crab.mm"
include "cint.mm"
include "wa.mm"
include "ssun1.mm"
include "ssintub.mm"
include "sstri.mm"
include "ssun2.mm"
include "pm3.2i.mm"
include "c0.mm"
include "wne.mm"
include "wcel.mm"
include "ssrab2.mm"
include "wrex.mm"
include "shscli.mm"
include "shunssi.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mp2an.mm"
include "rabn0.mm"
include "mpbir.mm"
include "shintcl.mm"
include "shslubi.mm"
include "mpbi.mm"
include "elrab.mm"
include "mpbir2an.mm"
include "intss1.mm"
include "ax-mp.mm"
include "eqssi.mm"

theorem shsval2i
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume shlesb1.1: |- A e. SH
  assume shlesb1.2: |- B e. SH

  disjoint A x
  disjoint B x
  assert |- ( A +H B ) = |^| { x e. SH | ( A u. B ) C_ x }

  proof
    cA
    cB
    cph
    co
    #
    cA
    cB
    cun
    #
    vx
    cv
    #
    wss
    #
    vx
    csh
    crab
    #
    cint
    #
    cA
    @5
    wss
    #
    cB
    @5
    wss
    #
    wa
    @0
    @5
    wss
    @6
    @7
    cA
    @1
    @5
    cA
    cB
    ssun1
    vx
    @1
    csh
    ssintub
    #
    sstri
    cB
    @1
    @5
    cB
    cA
    ssun2
    @8
    sstri
    pm3.2i
    cA
    cB
    @5
    shlesb1.1
    shlesb1.2
    @4
    csh
    wss
    @4
    c0
    wne
    #
    @5
    csh
    wcel
    @3
    vx
    csh
    ssrab2
    @9
    @3
    vx
    csh
    wrex
    #
    @0
    csh
    wcel
    #
    @1
    @0
    wss
    #
    @10
    cA
    cB
    shlesb1.1
    shlesb1.2
    shscli
    #
    cA
    cB
    shlesb1.1
    shlesb1.2
    shunssi
    #
    @3
    @12
    vx
    @0
    csh
    @2
    @0
    @1
    sseq2
    #
    rspcev
    mp2an
    @3
    vx
    csh
    rabn0
    mpbir
    @4
    shintcl
    mp2an
    shslubi
    mpbi
    @0
    @4
    wcel
    #
    @5
    @0
    wss
    @16
    @11
    @12
    @13
    @14
    @3
    @12
    vx
    @0
    csh
    @15
    elrab
    mpbir2an
    @0
    @4
    intss1
    ax-mp
    eqssi
end
