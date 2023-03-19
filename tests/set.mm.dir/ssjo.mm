include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cun.mm"
include "wceq.mm"
include "ocss.mm"
include "sshjval.mm"
include "mpdan.mm"
include "c0h.mm"
include "cin.mm"
include "ssun1.mm"
include "wi.mm"
include "wa.mm"
include "ancli.mm"
include "unss.mm"
include "sylib.mm"
include "occon.mm"
include "mpi.mm"
include "ssun2.mm"
include "syl2anc.mm"
include "ssind.mm"
include "csh.mm"
include "wcel.mm"
include "ocsh.mm"
include "ocin.mm"
include "syl.mm"
include "sseqtrd.mm"
include "sh0le.mm"
include "3syl.mm"
include "eqssd.mm"
include "fveq2d.mm"
include "choc0.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem ssjo
  let cA: class A


  assert |- ( A C_ ~H -> ( A vH ( _|_ ` A ) ) = ~H )

  proof
    cA
    chil
    wss
    #
    cA
    cA
    cort
    cfv
    #
    chj
    co
    #
    cA
    @1
    cun
    #
    cort
    cfv
    #
    cort
    cfv
    #
    chil
    @0
    @1
    chil
    wss
    #
    @2
    @5
    wceq
    cA
    ocss
    #
    cA
    @1
    sshjval
    mpdan
    @0
    @5
    c0h
    cort
    cfv
    chil
    @0
    @4
    c0h
    cort
    @0
    @4
    c0h
    @0
    @4
    @1
    @1
    cort
    cfv
    #
    cin
    #
    c0h
    @0
    @4
    @1
    @8
    @0
    cA
    @3
    wss
    #
    @4
    @1
    wss
    #
    cA
    @1
    ssun1
    @0
    @3
    chil
    wss
    #
    @10
    @11
    wi
    @0
    @0
    @6
    wa
    @12
    @0
    @6
    @7
    ancli
    cA
    @1
    chil
    unss
    sylib
    #
    cA
    @3
    occon
    mpdan
    mpi
    @0
    @1
    @3
    wss
    #
    @4
    @8
    wss
    #
    @1
    cA
    ssun2
    @0
    @6
    @12
    @14
    @15
    wi
    @7
    @13
    @1
    @3
    occon
    syl2anc
    mpi
    ssind
    @0
    @1
    csh
    wcel
    @9
    c0h
    wceq
    cA
    ocsh
    @1
    ocin
    syl
    sseqtrd
    @0
    @12
    @4
    csh
    wcel
    c0h
    @4
    wss
    @13
    @3
    ocsh
    @4
    sh0le
    3syl
    eqssd
    fveq2d
    choc0
    syl6eq
    eqtrd
end
