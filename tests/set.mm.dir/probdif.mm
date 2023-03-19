include "cprb.mm"
include "wcel.mm"
include "cdm.mm"
include "w3a.mm"
include "cfv.mm"
include "cin.mm"
include "cmin.mm"
include "co.mm"
include "cdif.mm"
include "caddc.mm"
include "cun.mm"
include "inundif.mm"
include "fveq2i.mm"
include "wceq.mm"
include "simp1.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "domprobsiga.mm"
include "inelsiga.mm"
include "syl3an1.mm"
include "difelsiga.mm"
include "c0.mm"
include "inindif.mm"
include "probun.mm"
include "mpi.mm"
include "syl3anc.mm"
include "syl5eqr.mm"
include "oveq1d.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cc.mm"
include "unitsscn.mm"
include "prob01.mm"
include "syl2anc.mm"
include "sseldi.mm"
include "pncan2d.mm"
include "eqtr2d.mm"

theorem probdif
  let cA: class A
  let cB: class B
  let cP: class P


  assert |- ( ( P e. Prob /\ A e. dom P /\ B e. dom P ) -> ( P ` ( A \ B ) ) = ( ( P ` A ) - ( P ` ( A i^i B ) ) ) )

  proof
    cP
    cprb
    wcel
    #
    cA
    cP
    cdm
    #
    wcel
    #
    cB
    @1
    wcel
    #
    w3a
    #
    cA
    cP
    cfv
    #
    cA
    cB
    cin
    #
    cP
    cfv
    #
    cmin
    co
    @7
    cA
    cB
    cdif
    #
    cP
    cfv
    #
    caddc
    co
    #
    @7
    cmin
    co
    @9
    @4
    @5
    @10
    @7
    cmin
    @4
    @5
    @6
    @8
    cun
    #
    cP
    cfv
    #
    @10
    @11
    cA
    cP
    cA
    cB
    inundif
    fveq2i
    @4
    @0
    @6
    @1
    wcel
    #
    @8
    @1
    wcel
    #
    @12
    @10
    wceq
    #
    @0
    @2
    @3
    simp1
    #
    @0
    @1
    csiga
    crn
    cuni
    wcel
    #
    @2
    @3
    @13
    cP
    domprobsiga
    #
    cA
    cB
    @1
    inelsiga
    syl3an1
    #
    @0
    @17
    @2
    @3
    @14
    @18
    cA
    cB
    @1
    difelsiga
    syl3an1
    #
    @0
    @13
    @14
    w3a
    @6
    @8
    cin
    c0
    wceq
    @15
    cA
    cB
    inindif
    @6
    @8
    cP
    probun
    mpi
    syl3anc
    syl5eqr
    oveq1d
    @4
    @7
    @9
    @4
    cc0
    c1
    cicc
    co
    #
    cc
    @7
    unitsscn
    @4
    @0
    @13
    @7
    @21
    wcel
    @16
    @19
    @6
    cP
    prob01
    syl2anc
    sseldi
    @4
    @21
    cc
    @9
    unitsscn
    @4
    @0
    @14
    @9
    @21
    wcel
    @16
    @20
    @8
    cP
    prob01
    syl2anc
    sseldi
    pncan2d
    eqtr2d
end
