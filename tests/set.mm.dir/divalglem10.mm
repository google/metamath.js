include "cc0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "w3a.mm"
include "cz.mm"
include "wrex.mm"
include "wreu.mm"
include "cr.mm"
include "cinf.mm"
include "eqid.mm"
include "divalglem9.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "cn0.mm"
include "elnn0z.mm"
include "anbi2i.mm"
include "an12.mm"
include "ancom.mm"
include "bitri.mm"
include "anbi1i.mm"
include "anass.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "divalglem4.mm"
include "elrab2.mm"
include "3bitr4i.mm"
include "df-3an.mm"
include "rexbii.mm"
include "r19.42v.mm"
include "eubii.mm"
include "df-reu.mm"
include "mpbi.mm"
include "breq2.mm"
include "breq1.mm"
include "3anbi123d.mm"
include "cbvreuv.mm"

theorem divalglem10
  let cD: class D
  let cS: class S
  let cN: class N
  let vr: setvar r
  let vq: setvar q
  let vx: setvar x
  let vz: setvar z
  let cX: class X
  let cY: class Y
  assume divalglem8.1: |- N e. ZZ
  assume divalglem8.2: |- D e. ZZ
  assume divalglem8.3: |- D =/= 0
  assume divalglem8.4: |- S = { r e. NN0 | D || ( N - r ) }

  disjoint D q
  disjoint D r
  disjoint q r
  disjoint N q
  disjoint N r
  disjoint D x
  disjoint D z
  disjoint q x
  disjoint q z
  disjoint r x
  disjoint r z
  disjoint x z
  disjoint N x
  disjoint N z
  disjoint S x
  disjoint S z
  disjoint X z
  disjoint Y z
  assert |- E! r e. ZZ E. q e. ZZ ( 0 <_ r /\ r < ( abs ` D ) /\ N = ( ( q x. D ) + r ) )

  proof
    cc0
    vx
    cv
    #
    cle
    wbr
    #
    @0
    cD
    cabs
    cfv
    #
    clt
    wbr
    #
    cN
    vq
    cv
    cD
    cmul
    co
    #
    @0
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cz
    wrex
    #
    vx
    cz
    wreu
    #
    cc0
    vr
    cv
    #
    cle
    wbr
    #
    @10
    @2
    clt
    wbr
    #
    cN
    @4
    @10
    caddc
    co
    #
    wceq
    #
    w3a
    #
    vq
    cz
    wrex
    #
    vr
    cz
    wreu
    @3
    vx
    cS
    wreu
    #
    @9
    vx
    cD
    cS
    cr
    clt
    cinf
    #
    cS
    cN
    vr
    divalglem8.1
    divalglem8.2
    divalglem8.3
    divalglem8.4
    @18
    eqid
    divalglem9
    @0
    cS
    wcel
    #
    @3
    wa
    #
    vx
    weu
    @0
    cz
    wcel
    #
    @8
    wa
    #
    vx
    weu
    @17
    @9
    @20
    @22
    vx
    @3
    @0
    cn0
    wcel
    #
    wa
    #
    @6
    vq
    cz
    wrex
    #
    wa
    #
    @21
    @1
    @3
    wa
    #
    @25
    wa
    #
    wa
    #
    @20
    @22
    @26
    @21
    @27
    wa
    #
    @25
    wa
    @29
    @24
    @30
    @25
    @24
    @3
    @21
    @1
    wa
    #
    wa
    #
    @30
    @23
    @31
    @3
    @0
    elnn0z
    anbi2i
    @32
    @21
    @3
    @1
    wa
    #
    wa
    @30
    @3
    @21
    @1
    an12
    @33
    @27
    @21
    @3
    @1
    ancom
    anbi2i
    bitri
    bitri
    anbi1i
    @21
    @27
    @25
    anass
    bitri
    @3
    @19
    wa
    @3
    @23
    @25
    wa
    #
    wa
    @20
    @26
    @19
    @34
    @3
    @14
    vq
    cz
    wrex
    @25
    vr
    @0
    cn0
    cS
    @10
    @0
    wceq
    #
    @14
    @6
    vq
    cz
    @35
    @13
    @5
    cN
    @10
    @0
    @4
    caddc
    oveq2
    eqeq2d
    rexbidv
    cD
    cS
    cN
    vr
    vq
    divalglem8.1
    divalglem8.2
    divalglem8.3
    divalglem8.4
    divalglem4
    elrab2
    anbi2i
    @19
    @3
    ancom
    @3
    @23
    @25
    anass
    3bitr4i
    @8
    @28
    @21
    @8
    @27
    @6
    wa
    #
    vq
    cz
    wrex
    @28
    @7
    @36
    vq
    cz
    @1
    @3
    @6
    df-3an
    rexbii
    @27
    @6
    vq
    cz
    r19.42v
    bitri
    anbi2i
    3bitr4i
    eubii
    @3
    vx
    cS
    df-reu
    @8
    vx
    cz
    df-reu
    3bitr4i
    mpbi
    @8
    @16
    vx
    vr
    cz
    @0
    @10
    wceq
    #
    @7
    @15
    vq
    cz
    @37
    @1
    @11
    @3
    @12
    @6
    @14
    @0
    @10
    cc0
    cle
    breq2
    @0
    @10
    @2
    clt
    breq1
    @37
    @5
    @13
    cN
    @0
    @10
    @4
    caddc
    oveq2
    eqeq2d
    3anbi123d
    rexbidv
    cbvreuv
    mpbi
end
