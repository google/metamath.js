include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "cn0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wrex.mm"
include "eqcom.mm"
include "cmin.mm"
include "cdvds.mm"
include "wb.mm"
include "divalgmodcl.mm"
include "3adant3r.mm"
include "ibar.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "nnz.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "nn0z.mm"
include "adantr.mm"
include "zsubcld.mm"
include "divides.mm"
include "syl2anc.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant1.mm"
include "nn0cn.mm"
include "simpr.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "subadd2d.mm"
include "syl5bb.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "3bitr2d.mm"

theorem modremain
  let vz: setvar z
  let cD: class D
  let cR: class R
  let cN: class N

  disjoint D z
  disjoint N z
  disjoint R z
  assert |- ( ( N e. ZZ /\ D e. NN /\ ( R e. NN0 /\ R < D ) ) -> ( ( N mod D ) = R <-> E. z e. ZZ ( ( z x. D ) + R ) = N ) )

  proof
    cN
    cD
    cmo
    co
    #
    cR
    wceq
    cR
    @0
    wceq
    #
    cN
    cz
    wcel
    #
    cD
    cn
    wcel
    #
    cR
    cn0
    wcel
    #
    cR
    cD
    clt
    wbr
    #
    wa
    #
    w3a
    #
    vz
    cv
    #
    cD
    cmul
    co
    #
    cR
    caddc
    co
    cN
    wceq
    #
    vz
    cz
    wrex
    #
    @0
    cR
    eqcom
    @7
    @1
    @5
    cD
    cN
    cR
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    @13
    @11
    @2
    @3
    @4
    @1
    @14
    wb
    @5
    cD
    cR
    cN
    divalgmodcl
    3adant3r
    @6
    @2
    @13
    @14
    wb
    #
    @3
    @5
    @15
    @4
    @5
    @13
    ibar
    adantl
    3ad2ant3
    @7
    @13
    @9
    @12
    wceq
    #
    vz
    cz
    wrex
    #
    @11
    @7
    cD
    cz
    wcel
    #
    @12
    cz
    wcel
    @13
    @17
    wb
    @3
    @2
    @18
    @6
    cD
    nnz
    3ad2ant2
    #
    @7
    cN
    cR
    @2
    @3
    @6
    simp1
    @6
    @2
    cR
    cz
    wcel
    #
    @3
    @4
    @20
    @5
    cR
    nn0z
    adantr
    3ad2ant3
    zsubcld
    vz
    cD
    @12
    divides
    syl2anc
    @7
    @16
    @10
    vz
    cz
    @16
    @12
    @9
    wceq
    @7
    @8
    cz
    wcel
    #
    wa
    #
    @10
    @9
    @12
    eqcom
    @22
    cN
    cR
    @9
    @7
    cN
    cc
    wcel
    #
    @21
    @2
    @3
    @23
    @6
    cN
    zcn
    3ad2ant1
    adantr
    @7
    cR
    cc
    wcel
    #
    @21
    @6
    @2
    @24
    @3
    @4
    @24
    @5
    cR
    nn0cn
    adantr
    3ad2ant3
    adantr
    @22
    @9
    @22
    @8
    cD
    @7
    @21
    simpr
    @7
    @18
    @21
    @19
    adantr
    zmulcld
    zcnd
    subadd2d
    syl5bb
    rexbidva
    bitrd
    3bitr2d
    syl5bb
end
