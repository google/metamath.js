include "cat.mm"
include "wcel.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "wn.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "inass.mm"
include "chjcomi.mm"
include "ineq1i.mm"
include "incom.mm"
include "chabs2i.mm"
include "3eqtri.mm"
include "ineq2i.mm"
include "eqtr2i.mm"
include "chub1i.mm"
include "cch.mm"
include "cmd.mm"
include "wbr.mm"
include "wi.mm"
include "atelch.mm"
include "chjcli.mm"
include "atmd.mm"
include "mpan2.mm"
include "w3a.mm"
include "mdi.mm"
include "exp32.mm"
include "mp3an23.mm"
include "sylc.mm"
include "mpi.mm"
include "adantr.mm"
include "c0h.mm"
include "wb.mm"
include "atnssm0.mm"
include "mpan.mm"
include "biimpa.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "chj0i.mm"
include "syl6eq.mm"
include "eqtrd.mm"
include "ineq1d.mm"
include "ex.mm"

theorem atabsi
  let cA: class A
  let cB: class B
  let cC: class C
  assume atabs.1: |- A e. CH
  assume atabs.2: |- B e. CH


  assert |- ( C e. HAtoms -> ( -. C C_ ( A vH B ) -> ( ( A vH C ) i^i B ) = ( A i^i B ) ) )

  proof
    cC
    cat
    wcel
    #
    cC
    cA
    cB
    chj
    co
    #
    wss
    wn
    #
    cA
    cC
    chj
    co
    #
    cB
    cin
    #
    cA
    cB
    cin
    #
    wceq
    @0
    @2
    wa
    #
    @4
    @3
    @1
    cin
    #
    cB
    cin
    #
    @5
    @8
    @3
    @1
    cB
    cin
    #
    cin
    @4
    @3
    @1
    cB
    inass
    @9
    cB
    @3
    @9
    cB
    cA
    chj
    co
    #
    cB
    cin
    cB
    @10
    cin
    cB
    @1
    @10
    cB
    cA
    cB
    atabs.1
    atabs.2
    chjcomi
    ineq1i
    @10
    cB
    incom
    cB
    cA
    atabs.2
    atabs.1
    chabs2i
    3eqtri
    ineq2i
    eqtr2i
    @6
    @7
    cA
    cB
    @6
    @7
    cA
    cC
    @1
    cin
    #
    chj
    co
    #
    cA
    @0
    @7
    @12
    wceq
    #
    @2
    @0
    cA
    @1
    wss
    #
    @13
    cA
    cB
    atabs.1
    atabs.2
    chub1i
    @0
    cC
    cch
    wcel
    #
    cC
    @1
    cmd
    wbr
    #
    @14
    @13
    wi
    #
    cC
    atelch
    @0
    @1
    cch
    wcel
    #
    @16
    cA
    cB
    atabs.1
    atabs.2
    chjcli
    #
    cC
    @1
    atmd
    mpan2
    @15
    @18
    cA
    cch
    wcel
    #
    @16
    @17
    wi
    @19
    atabs.1
    @15
    @18
    @20
    w3a
    @16
    @14
    @13
    cC
    @1
    cA
    mdi
    exp32
    mp3an23
    sylc
    mpi
    adantr
    @6
    @12
    cA
    c0h
    chj
    co
    cA
    @6
    @11
    c0h
    cA
    chj
    @6
    @11
    @1
    cC
    cin
    #
    c0h
    cC
    @1
    incom
    @0
    @2
    @21
    c0h
    wceq
    #
    @18
    @0
    @2
    @22
    wb
    @19
    @1
    cC
    atnssm0
    mpan
    biimpa
    syl5eq
    oveq2d
    cA
    atabs.1
    chj0i
    syl6eq
    eqtrd
    ineq1d
    syl5eq
    ex
end
