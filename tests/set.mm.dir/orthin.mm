include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "wi.mm"
include "ssrin.mm"
include "incom.mm"
include "syl6sseq.mm"
include "ocin.mm"
include "sseq2d.mm"
include "syl5ib.mm"
include "adantl.mm"
include "shincl.mm"
include "sh0le.mm"
include "syl.mm"
include "jctird.mm"
include "eqss.mm"
include "syl6ibr.mm"

theorem orthin
  let cA: class A
  let cB: class B


  assert |- ( ( A e. SH /\ B e. SH ) -> ( A C_ ( _|_ ` B ) -> ( A i^i B ) = 0H ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    wa
    #
    cA
    cB
    cort
    cfv
    #
    wss
    #
    cA
    cB
    cin
    #
    c0h
    wss
    #
    c0h
    @5
    wss
    #
    wa
    @5
    c0h
    wceq
    @2
    @4
    @6
    @7
    @1
    @4
    @6
    wi
    @0
    @4
    @5
    cB
    @3
    cin
    #
    wss
    @1
    @6
    @4
    @5
    @3
    cB
    cin
    @8
    cA
    @3
    cB
    ssrin
    @3
    cB
    incom
    syl6sseq
    @1
    @8
    c0h
    @5
    cB
    ocin
    sseq2d
    syl5ib
    adantl
    @2
    @5
    csh
    wcel
    @7
    cA
    cB
    shincl
    @5
    sh0le
    syl
    jctird
    @5
    c0h
    eqss
    syl6ibr
end
