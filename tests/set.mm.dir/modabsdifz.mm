include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cabs.mm"
include "cfv.mm"
include "cmo.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "cz.mm"
include "crp.mm"
include "simp1.mm"
include "simp2.mm"
include "recnd.mm"
include "simp3.mm"
include "absrpcld.mm"
include "moddifz.mm"
include "syl2anc.mm"
include "cc.mm"
include "wceq.mm"
include "absidm.mm"
include "syl.mm"
include "oveq2d.mm"
include "modcld.mm"
include "resubcld.mm"
include "abscld.mm"
include "rpne0d.mm"
include "absdivd.mm"
include "3eqtr4d.mm"
include "eleq1d.mm"
include "wb.mm"
include "redivcld.mm"
include "absz.mm"
include "3bitr4d.mm"
include "mpbid.mm"

theorem modabsdifz
  let cM: class M
  let cN: class N


  assert |- ( ( N e. RR /\ M e. RR /\ M =/= 0 ) -> ( ( N - ( N mod ( abs ` M ) ) ) / M ) e. ZZ )

  proof
    cN
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    cM
    cc0
    wne
    #
    w3a
    #
    cN
    cN
    cM
    cabs
    cfv
    #
    cmo
    co
    #
    cmin
    co
    #
    @4
    cdiv
    co
    #
    cz
    wcel
    #
    @6
    cM
    cdiv
    co
    #
    cz
    wcel
    #
    @3
    @0
    @4
    crp
    wcel
    @8
    @0
    @1
    @2
    simp1
    #
    @3
    cM
    @3
    cM
    @0
    @1
    @2
    simp2
    #
    recnd
    #
    @0
    @1
    @2
    simp3
    #
    absrpcld
    #
    cN
    @4
    moddifz
    syl2anc
    @3
    @7
    cabs
    cfv
    #
    cz
    wcel
    #
    @9
    cabs
    cfv
    #
    cz
    wcel
    #
    @8
    @10
    @3
    @16
    @18
    cz
    @3
    @6
    cabs
    cfv
    #
    @4
    cabs
    cfv
    #
    cdiv
    co
    @20
    @4
    cdiv
    co
    @16
    @18
    @3
    @21
    @4
    @20
    cdiv
    @3
    cM
    cc
    wcel
    @21
    @4
    wceq
    @13
    cM
    absidm
    syl
    oveq2d
    @3
    @6
    @4
    @3
    @6
    @3
    cN
    @5
    @11
    @3
    cN
    @4
    @11
    @15
    modcld
    resubcld
    #
    recnd
    #
    @3
    @4
    @3
    cM
    @13
    abscld
    #
    recnd
    @3
    @4
    @15
    rpne0d
    #
    absdivd
    @3
    @6
    cM
    @23
    @13
    @14
    absdivd
    3eqtr4d
    eleq1d
    @3
    @7
    cr
    wcel
    @8
    @17
    wb
    @3
    @6
    @4
    @22
    @24
    @25
    redivcld
    @7
    absz
    syl
    @3
    @9
    cr
    wcel
    @10
    @19
    wb
    @3
    @6
    cM
    @22
    @12
    @14
    redivcld
    @9
    absz
    syl
    3bitr4d
    mpbid
end
