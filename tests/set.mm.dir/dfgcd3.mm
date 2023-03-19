include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "cn0.mm"
include "crio.mm"
include "cgcd.mm"
include "co.mm"
include "gcdcl.mm"
include "wceq.mm"
include "wi.mm"
include "simplr.mm"
include "nn0zd.mm"
include "iddvds.mm"
include "syl.mm"
include "simpr.mm"
include "breq1.mm"
include "anbi12d.mm"
include "bibi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "mpbid.mm"
include "biimpr.mm"
include "ralimi.mm"
include "cc0.mm"
include "cle.mm"
include "w3a.mm"
include "dfgcd2.mm"
include "adantr.mm"
include "nn0ge0d.mm"
include "3biant1d.mm"
include "bitr4d.mm"
include "mpbir2and.mm"
include "ex.mm"
include "dvdsgcdb.mm"
include "bicomd.mm"
include "3coml.mm"
include "ad4ant124.mm"
include "breq2.mm"
include "bibi1d.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "ralrimiva.mm"
include "impbid.mm"
include "riota5.mm"
include "eqcomd.mm"

theorem dfgcd3
  let vz: setvar z
  let cM: class M
  let cN: class N
  let vd: setvar d

  disjoint M d
  disjoint M z
  disjoint d z
  disjoint N d
  disjoint N z
  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M gcd N ) = ( iota_ d e. NN0 A. z e. ZZ ( z || d <-> ( z || M /\ z || N ) ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    vz
    cv
    #
    vd
    cv
    #
    cdvds
    wbr
    #
    @3
    cM
    cdvds
    wbr
    #
    @3
    cN
    cdvds
    wbr
    #
    wa
    #
    wb
    #
    vz
    cz
    wral
    #
    vd
    cn0
    crio
    cM
    cN
    cgcd
    co
    #
    @2
    @10
    vd
    cn0
    @11
    cM
    cN
    gcdcl
    @2
    @4
    cn0
    wcel
    #
    wa
    #
    @10
    @4
    @11
    wceq
    #
    @13
    @10
    @14
    @13
    @10
    wa
    #
    @14
    @4
    cM
    cdvds
    wbr
    #
    @4
    cN
    cdvds
    wbr
    #
    wa
    #
    @8
    @5
    wi
    #
    vz
    cz
    wral
    #
    @15
    @4
    @4
    cdvds
    wbr
    #
    @18
    @15
    @4
    cz
    wcel
    #
    @21
    @15
    @4
    @2
    @12
    @10
    simplr
    nn0zd
    #
    @4
    iddvds
    syl
    @15
    @22
    @10
    @21
    @18
    wb
    #
    @23
    @13
    @10
    simpr
    #
    @9
    @24
    vz
    @4
    cz
    @3
    @4
    wceq
    #
    @5
    @21
    @8
    @18
    @3
    @4
    @4
    cdvds
    breq1
    @26
    @6
    @16
    @7
    @17
    @3
    @4
    cM
    cdvds
    breq1
    @3
    @4
    cN
    cdvds
    breq1
    anbi12d
    bibi12d
    rspcv
    sylc
    mpbid
    @15
    @10
    @20
    @25
    @9
    @19
    vz
    cz
    @5
    @8
    biimpr
    ralimi
    syl
    @13
    @14
    @18
    @20
    wa
    #
    wb
    @10
    @13
    @14
    cc0
    @4
    cle
    wbr
    #
    @18
    @20
    w3a
    #
    @27
    @2
    @14
    @29
    wb
    @12
    @4
    vz
    cM
    cN
    dfgcd2
    adantr
    @13
    @20
    @18
    @28
    @13
    @4
    @2
    @12
    simpr
    nn0ge0d
    3biant1d
    bitr4d
    adantr
    mpbir2and
    ex
    @2
    @14
    @10
    wi
    @12
    @2
    @14
    @10
    @2
    @14
    wa
    #
    @9
    vz
    cz
    @30
    @3
    cz
    wcel
    #
    wa
    @9
    @3
    @11
    cdvds
    wbr
    #
    @8
    wb
    #
    @0
    @1
    @31
    @33
    @14
    @31
    @0
    @1
    @33
    @31
    @0
    @1
    w3a
    @8
    @32
    @3
    cM
    cN
    dvdsgcdb
    bicomd
    3coml
    ad4ant124
    @14
    @9
    @33
    wb
    @2
    @31
    @14
    @5
    @32
    @8
    @4
    @11
    @3
    cdvds
    breq2
    bibi1d
    ad2antlr
    mpbird
    ralrimiva
    ex
    adantr
    impbid
    riota5
    eqcomd
end
