include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cv.mm"
include "cch.mm"
include "crab.mm"
include "cint.mm"
include "wa.mm"
include "wcel.mm"
include "helch.mm"
include "jctl.mm"
include "sseq2.mm"
include "elrab.mm"
include "sylibr.mm"
include "intss1.mm"
include "syl.mm"
include "ocss.mm"
include "jca.mm"
include "ssintub.mm"
include "wi.mm"
include "occon.mm"
include "mpdan.mm"
include "mpi.mm"
include "sylc.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "wrex.mm"
include "rspcev.mm"
include "mpan.mm"
include "rabn0.mm"
include "chintcl.mm"
include "sylancr.mm"
include "ococ.mm"
include "sseqtrd.mm"
include "occl.mm"
include "ococss.mm"
include "sylanbrc.mm"
include "eqssd.mm"

theorem ococin
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint A y
  disjoint B x
  assert |- ( A C_ ~H -> ( _|_ ` ( _|_ ` A ) ) = |^| { x e. CH | A C_ x } )

  proof
    cA
    chil
    wss
    #
    cA
    cort
    cfv
    #
    cort
    cfv
    #
    cA
    vx
    cv
    #
    wss
    #
    vx
    cch
    crab
    #
    cint
    #
    @0
    @2
    @6
    cort
    cfv
    #
    cort
    cfv
    #
    @6
    @0
    @7
    chil
    wss
    #
    @1
    chil
    wss
    #
    wa
    @7
    @1
    wss
    #
    @2
    @8
    wss
    @0
    @9
    @10
    @0
    @6
    chil
    wss
    #
    @9
    @0
    chil
    @5
    wcel
    #
    @12
    @0
    chil
    cch
    wcel
    #
    @0
    wa
    @13
    @0
    @14
    helch
    jctl
    @4
    @0
    vx
    chil
    cch
    @3
    chil
    cA
    sseq2
    #
    elrab
    sylibr
    chil
    @5
    intss1
    syl
    #
    @6
    ocss
    syl
    cA
    ocss
    #
    jca
    @0
    cA
    @6
    wss
    #
    @11
    vx
    cA
    cch
    ssintub
    @0
    @12
    @18
    @11
    wi
    @16
    cA
    @6
    occon
    mpdan
    mpi
    @7
    @1
    occon
    sylc
    @0
    @6
    cch
    wcel
    #
    @8
    @6
    wceq
    @0
    @5
    cch
    wss
    @5
    c0
    wne
    #
    @19
    @4
    vx
    cch
    ssrab2
    @0
    @4
    vx
    cch
    wrex
    #
    @20
    @14
    @0
    @21
    helch
    @4
    @0
    vx
    chil
    cch
    @15
    rspcev
    mpan
    @4
    vx
    cch
    rabn0
    sylibr
    @5
    chintcl
    sylancr
    @6
    ococ
    syl
    sseqtrd
    @0
    @2
    @5
    wcel
    #
    @6
    @2
    wss
    @0
    @2
    cch
    wcel
    #
    cA
    @2
    wss
    #
    @22
    @0
    @10
    @23
    @17
    @1
    occl
    syl
    cA
    ococss
    @4
    @24
    vx
    @2
    cch
    @3
    @2
    cA
    sseq2
    elrab
    sylanbrc
    @2
    @5
    intss1
    syl
    eqssd
end
