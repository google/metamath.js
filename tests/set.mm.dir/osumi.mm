include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cph.mm"
include "co.mm"
include "cch.mm"
include "wcel.mm"
include "chj.mm"
include "wceq.mm"
include "a1i.mm"
include "chsscon2i.mm"
include "biimpi.mm"
include "chscl.mm"
include "chshii.mm"
include "shjshseli.mm"
include "sylib.mm"

theorem osumi
  let cA: class A
  let cB: class B
  assume osum.1: |- A e. CH
  assume osum.2: |- B e. CH


  assert |- ( A C_ ( _|_ ` B ) -> ( A +H B ) = ( A vH B ) )

  proof
    cA
    cB
    cort
    cfv
    wss
    #
    cA
    cB
    cph
    co
    #
    cch
    wcel
    @1
    cA
    cB
    chj
    co
    wceq
    @0
    cA
    cB
    cA
    cch
    wcel
    @0
    osum.1
    a1i
    cB
    cch
    wcel
    @0
    osum.2
    a1i
    @0
    cB
    cA
    cort
    cfv
    wss
    cA
    cB
    osum.1
    osum.2
    chsscon2i
    biimpi
    chscl
    cA
    cB
    cA
    osum.1
    chshii
    cB
    osum.2
    chshii
    shjshseli
    sylib
end
