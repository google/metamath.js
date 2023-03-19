include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "cmul.mm"
include "caddc.mm"
include "iddvds.mm"
include "wb.mm"
include "dvdsabsb.mm"
include "anidms.mm"
include "mpbid.mm"
include "ax-mp.mm"
include "wi.mm"
include "cn0.mm"
include "nn0abscl.mm"
include "nn0zi.mm"
include "dvdsmultr2.mm"
include "mp3an13.mm"
include "mpi.mm"
include "adantl.mm"
include "zsubcl.mm"
include "mpan.mm"
include "zmulcl.mm"
include "mpan2.mm"
include "dvds2add.mm"
include "mp3an1.mm"
include "syl2an.mm"
include "mpan2d.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "zcnd.mm"
include "subsub.mm"
include "breq2d.mm"
include "sylibrd.mm"

theorem divalglem0
  let cD: class D
  let cR: class R
  let cK: class K
  let cN: class N
  assume divalglem0.1: |- N e. ZZ
  assume divalglem0.2: |- D e. ZZ


  assert |- ( ( R e. ZZ /\ K e. ZZ ) -> ( D || ( N - R ) -> D || ( N - ( R - ( K x. ( abs ` D ) ) ) ) ) )

  proof
    cR
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    wa
    #
    cD
    cN
    cR
    cmin
    co
    #
    cdvds
    wbr
    #
    cD
    @3
    cK
    cD
    cabs
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    cdvds
    wbr
    #
    cD
    cN
    cR
    @6
    cmin
    co
    cmin
    co
    #
    cdvds
    wbr
    @2
    @4
    cD
    @6
    cdvds
    wbr
    #
    @8
    @1
    @10
    @0
    @1
    cD
    @5
    cdvds
    wbr
    #
    @10
    cD
    cz
    wcel
    #
    @11
    divalglem0.2
    @12
    cD
    cD
    cdvds
    wbr
    #
    @11
    cD
    iddvds
    @12
    @13
    @11
    wb
    cD
    cD
    dvdsabsb
    anidms
    mpbid
    ax-mp
    @12
    @1
    @5
    cz
    wcel
    #
    @11
    @10
    wi
    divalglem0.2
    @5
    @12
    @5
    cn0
    wcel
    divalglem0.2
    cD
    nn0abscl
    ax-mp
    nn0zi
    #
    cD
    cK
    @5
    dvdsmultr2
    mp3an13
    mpi
    adantl
    @0
    @3
    cz
    wcel
    #
    @6
    cz
    wcel
    #
    @4
    @10
    wa
    @8
    wi
    #
    @1
    cN
    cz
    wcel
    #
    @0
    @16
    divalglem0.1
    cN
    cR
    zsubcl
    mpan
    @1
    @14
    @17
    @15
    cK
    @5
    zmulcl
    mpan2
    #
    @12
    @16
    @17
    @18
    divalglem0.2
    cD
    @3
    @6
    dvds2add
    mp3an1
    syl2an
    mpan2d
    @2
    @9
    @7
    cD
    cdvds
    @0
    cR
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    @9
    @7
    wceq
    #
    @1
    cR
    zcn
    @1
    @6
    @20
    zcnd
    cN
    cc
    wcel
    #
    @21
    @22
    @23
    @19
    @24
    divalglem0.1
    cN
    zcn
    ax-mp
    cN
    cR
    @6
    subsub
    mp3an1
    syl2an
    breq2d
    sylibrd
end
