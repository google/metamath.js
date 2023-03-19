include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cph.mm"
include "co.mm"
include "chj.mm"
include "wceq.mm"
include "inss2.mm"
include "choccli.mm"
include "chub2i.mm"
include "sstri.mm"
include "chdmm3i.mm"
include "sseqtr4i.mm"
include "chincli.mm"
include "osumi.mm"
include "ax-mp.mm"

theorem osumcori
  let cA: class A
  let cB: class B
  assume osum.1: |- A e. CH
  assume osum.2: |- B e. CH


  assert |- ( ( A i^i B ) +H ( A i^i ( _|_ ` B ) ) ) = ( ( A i^i B ) vH ( A i^i ( _|_ ` B ) ) )

  proof
    cA
    cB
    cin
    #
    cA
    cB
    cort
    cfv
    #
    cin
    #
    cort
    cfv
    #
    wss
    @0
    @2
    cph
    co
    @0
    @2
    chj
    co
    wceq
    @0
    cA
    cort
    cfv
    #
    cB
    chj
    co
    #
    @3
    @0
    cB
    @5
    cA
    cB
    inss2
    cB
    @4
    osum.2
    cA
    osum.1
    choccli
    chub2i
    sstri
    cA
    cB
    osum.1
    osum.2
    chdmm3i
    sseqtr4i
    @0
    @2
    cA
    cB
    osum.1
    osum.2
    chincli
    cA
    @1
    osum.1
    cB
    osum.2
    choccli
    chincli
    osumi
    ax-mp
end
