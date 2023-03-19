include "cc0.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "wcel.mm"
include "cn0.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nn0uz.mm"
include "sseqtri.mm"
include "cmul.mm"
include "cabs.mm"
include "caddc.mm"
include "cz.mm"
include "cle.mm"
include "zmulcl.mm"
include "mp2an.mm"
include "nn0abscl.mm"
include "ax-mp.mm"
include "nn0zi.mm"
include "zaddcl.mm"
include "divalglem1.mm"
include "elnn0z.mm"
include "mpbir2an.mm"
include "cneg.mm"
include "iddvds.mm"
include "wb.mm"
include "dvdsabsb.mm"
include "anidms.mm"
include "mpbid.mm"
include "wi.mm"
include "nn0negzi.mm"
include "dvdsmultr2.mm"
include "mp3an.mm"
include "cc.mm"
include "zcn.mm"
include "absmuli.mm"
include "negeqi.mm"
include "df-neg.mm"
include "subidi.mm"
include "oveq1i.mm"
include "wceq.mm"
include "nn0cni.mm"
include "subsub4.mm"
include "3eqtr2ri.mm"
include "abscli.mm"
include "recni.mm"
include "mulneg1i.mm"
include "3eqtr4i.mm"
include "breqtrri.mm"
include "oveq2.mm"
include "breq2d.mm"
include "elrab2.mm"
include "ne0ii.mm"
include "infssuzcl.mm"

theorem divalglem2
  let cD: class D
  let cS: class S
  let cN: class N
  let vr: setvar r
  assume divalglem0.1: |- N e. ZZ
  assume divalglem0.2: |- D e. ZZ
  assume divalglem1.3: |- D =/= 0
  assume divalglem2.4: |- S = { r e. NN0 | D || ( N - r ) }

  disjoint D r
  disjoint N r
  assert |- inf ( S , RR , < ) e. S

  proof
    cS
    cc0
    cuz
    cfv
    #
    wss
    cS
    c0
    wne
    cS
    cr
    clt
    cinf
    cS
    wcel
    cS
    cn0
    @0
    cS
    cD
    cN
    vr
    cv
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    vr
    cn0
    crab
    cn0
    divalglem2.4
    @3
    vr
    cn0
    ssrab2
    eqsstri
    nn0uz
    sseqtri
    cN
    cN
    cD
    cmul
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    cS
    @6
    cS
    wcel
    @6
    cn0
    wcel
    #
    cD
    cN
    @6
    cmin
    co
    #
    cdvds
    wbr
    #
    @7
    @6
    cz
    wcel
    #
    cc0
    @6
    cle
    wbr
    cN
    cz
    wcel
    #
    @5
    cz
    wcel
    @10
    divalglem0.1
    @5
    @4
    cz
    wcel
    #
    @5
    cn0
    wcel
    @11
    cD
    cz
    wcel
    #
    @12
    divalglem0.1
    divalglem0.2
    cN
    cD
    zmulcl
    mp2an
    @4
    nn0abscl
    ax-mp
    #
    nn0zi
    cN
    @5
    zaddcl
    mp2an
    cD
    cN
    divalglem0.1
    divalglem0.2
    divalglem1.3
    divalglem1
    @6
    elnn0z
    mpbir2an
    cD
    cN
    cabs
    cfv
    #
    cneg
    #
    cD
    cabs
    cfv
    #
    cmul
    co
    #
    @8
    cdvds
    cD
    @17
    cdvds
    wbr
    #
    cD
    @18
    cdvds
    wbr
    #
    @13
    @19
    divalglem0.2
    @13
    cD
    cD
    cdvds
    wbr
    #
    @19
    cD
    iddvds
    @13
    @21
    @19
    wb
    cD
    cD
    dvdsabsb
    anidms
    mpbid
    ax-mp
    @13
    @16
    cz
    wcel
    @17
    cz
    wcel
    @19
    @20
    wi
    divalglem0.2
    @15
    @11
    @15
    cn0
    wcel
    divalglem0.1
    cN
    nn0abscl
    ax-mp
    nn0negzi
    @17
    @13
    @17
    cn0
    wcel
    divalglem0.2
    cD
    nn0abscl
    ax-mp
    nn0zi
    cD
    @16
    @17
    dvdsmultr2
    mp3an
    ax-mp
    @5
    cneg
    #
    @15
    @17
    cmul
    co
    #
    cneg
    @8
    @18
    @5
    @23
    cN
    cD
    @11
    cN
    cc
    wcel
    #
    divalglem0.1
    cN
    zcn
    ax-mp
    #
    @13
    cD
    cc
    wcel
    divalglem0.2
    cD
    zcn
    ax-mp
    #
    absmuli
    negeqi
    @22
    cc0
    @5
    cmin
    co
    cN
    cN
    cmin
    co
    #
    @5
    cmin
    co
    #
    @8
    @5
    df-neg
    @27
    cc0
    @5
    cmin
    cN
    @25
    subidi
    oveq1i
    @24
    @24
    @5
    cc
    wcel
    @28
    @8
    wceq
    @25
    @25
    @5
    @14
    nn0cni
    cN
    cN
    @5
    subsub4
    mp3an
    3eqtr2ri
    @15
    @17
    @15
    cN
    @25
    abscli
    recni
    @17
    cD
    @26
    abscli
    recni
    mulneg1i
    3eqtr4i
    breqtrri
    @3
    @9
    vr
    @6
    cn0
    cS
    @1
    @6
    wceq
    @2
    @8
    cD
    cdvds
    @1
    @6
    cN
    cmin
    oveq2
    breq2d
    divalglem2.4
    elrab2
    mpbir2an
    ne0ii
    cS
    cc0
    infssuzcl
    mp2an
end
