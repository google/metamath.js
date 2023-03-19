include "chj.mm"
include "co.mm"
include "chjcli.mm"
include "chshii.mm"
include "chub1i.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "wa.mm"
include "incom.mm"
include "choccli.mm"
include "cmj1i.mm"
include "cmcmii.mm"
include "cmcm2ii.mm"
include "cmj2i.mm"
include "fh1i.mm"
include "eqtr3i.mm"
include "chil.mm"
include "chjoi.mm"
include "choc0.mm"
include "chdmm1i.mm"
include "3eqtr4i.mm"
include "chincli.mm"
include "h0elch.mm"
include "chcon3i.mm"
include "mpbir.mm"
include "chj00i.mm"
include "simpli.mm"
include "omlsii.mm"
include "chub2i.mm"
include "simpri.mm"
include "eqtr4i.mm"

theorem qlaxr3i
  let cA: class A
  let cB: class B
  let cC: class C
  assume qlaxr3.1: |- A e. CH
  assume qlaxr3.2: |- B e. CH
  assume qlaxr3.3: |- C e. CH
  assume qlaxr3.4: |- ( C vH ( _|_ ` C ) ) = ( ( _|_ ` ( ( _|_ ` A ) vH ( _|_ ` B ) ) ) vH ( _|_ ` ( A vH B ) ) )


  assert |- A = B

  proof
    cA
    cA
    cB
    chj
    co
    #
    cB
    cA
    @0
    qlaxr3.1
    @0
    cA
    cB
    qlaxr3.1
    qlaxr3.2
    chjcli
    #
    chshii
    #
    cA
    cB
    qlaxr3.1
    qlaxr3.2
    chub1i
    @0
    cA
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    #
    @0
    cB
    cort
    cfv
    #
    cin
    #
    c0h
    wceq
    #
    @5
    @8
    wa
    @4
    @7
    chj
    co
    #
    c0h
    wceq
    @3
    @6
    chj
    co
    #
    @0
    cin
    #
    @9
    c0h
    @0
    @10
    cin
    @11
    @9
    @0
    @10
    incom
    @0
    @3
    @6
    @1
    cA
    qlaxr3.1
    choccli
    #
    cB
    qlaxr3.2
    choccli
    #
    @0
    cA
    @1
    qlaxr3.1
    cA
    @0
    qlaxr3.1
    @1
    cA
    cB
    qlaxr3.1
    qlaxr3.2
    cmj1i
    cmcmii
    cmcm2ii
    @0
    cB
    @1
    qlaxr3.2
    cB
    @0
    qlaxr3.2
    @1
    cA
    cB
    qlaxr3.1
    qlaxr3.2
    cmj2i
    cmcmii
    cmcm2ii
    fh1i
    eqtr3i
    @11
    c0h
    wceq
    c0h
    cort
    cfv
    #
    @11
    cort
    cfv
    #
    wceq
    chil
    @10
    cort
    cfv
    @0
    cort
    cfv
    chj
    co
    #
    @14
    @15
    cC
    cC
    cort
    cfv
    chj
    co
    chil
    @16
    cC
    qlaxr3.3
    chjoi
    qlaxr3.4
    eqtr3i
    choc0
    @10
    @0
    @3
    @6
    @12
    @13
    chjcli
    #
    @1
    chdmm1i
    3eqtr4i
    @11
    c0h
    @10
    @0
    @17
    @1
    chincli
    h0elch
    chcon3i
    mpbir
    eqtr3i
    @4
    @7
    @0
    @3
    @1
    @12
    chincli
    @0
    @6
    @1
    @13
    chincli
    chj00i
    mpbir
    #
    simpli
    omlsii
    cB
    @0
    qlaxr3.2
    @2
    cB
    cA
    qlaxr3.2
    qlaxr3.1
    chub2i
    @5
    @8
    @18
    simpri
    omlsii
    eqtr4i
end
