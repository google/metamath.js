include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "cn0.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wa.mm"
include "cr.mm"
include "cinf.mm"
include "divalglem2.mm"
include "eqeltri.mm"
include "cv.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq2d.mm"
include "crab.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "elrab2.mm"
include "mpbi.mm"
include "simpli.mm"
include "nn0ge0i.mm"
include "wn.mm"
include "cz.mm"
include "wne.mm"
include "cn.mm"
include "nnabscl.mm"
include "mp2an.mm"
include "nngt0i.mm"
include "0re.mm"
include "cc.mm"
include "zcn.mm"
include "ax-mp.mm"
include "abscli.mm"
include "ltnlei.mm"
include "cuz.mm"
include "wss.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nn0uz.mm"
include "sseqtri.mm"
include "nn0abscl.mm"
include "nn0sub2.mm"
include "mp3an12.mm"
include "a1i.mm"
include "wi.mm"
include "nn0z.mm"
include "c1.mm"
include "cmul.mm"
include "1z.mm"
include "divalglem0.mm"
include "mpan2.mm"
include "recni.mm"
include "mulid2i.mm"
include "oveq2i.mm"
include "breq2i.mm"
include "syl6ib.mm"
include "syl.mm"
include "imp.mm"
include "sylanbrc.mm"
include "infssuzle.mm"
include "sylancr.mm"
include "syl5eqbr.mm"
include "wb.mm"
include "simpld.mm"
include "nn0re.mm"
include "lesub.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "recnd.mm"
include "subidd.mm"
include "bitrd.mm"
include "mpbid.mm"
include "mto.mm"
include "mpbir.mm"
include "pm3.2i.mm"

theorem divalglem5
  let cD: class D
  let cR: class R
  let cS: class S
  let cN: class N
  let vr: setvar r
  let vq: setvar q
  let vx: setvar x
  let vz: setvar z
  assume divalglem0.1: |- N e. ZZ
  assume divalglem0.2: |- D e. ZZ
  assume divalglem1.3: |- D =/= 0
  assume divalglem2.4: |- S = { r e. NN0 | D || ( N - r ) }
  assume divalglem5.5: |- R = inf ( S , RR , < )

  disjoint D r
  disjoint N r
  disjoint D q
  disjoint D x
  disjoint D z
  disjoint q r
  disjoint q x
  disjoint q z
  disjoint r x
  disjoint r z
  disjoint x z
  disjoint N q
  disjoint N x
  disjoint N z
  disjoint R x
  disjoint S z
  assert |- ( 0 <_ R /\ R < ( abs ` D ) )

  proof
    cc0
    cR
    cle
    wbr
    cR
    cD
    cabs
    cfv
    #
    clt
    wbr
    #
    cR
    cR
    cn0
    wcel
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
    cR
    cS
    wcel
    @2
    @4
    wa
    #
    cR
    cS
    cr
    clt
    cinf
    #
    cS
    divalglem5.5
    cD
    cS
    cN
    vr
    divalglem0.1
    divalglem0.2
    divalglem1.3
    divalglem2.4
    divalglem2
    eqeltri
    cD
    cN
    vx
    cv
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    @4
    vx
    cR
    cn0
    cS
    @7
    cR
    wceq
    @8
    @3
    cD
    cdvds
    @7
    cR
    cN
    cmin
    oveq2
    breq2d
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
    #
    @9
    vx
    cn0
    crab
    divalglem2.4
    @12
    @9
    vr
    vx
    cn0
    @10
    @7
    wceq
    @11
    @8
    cD
    cdvds
    @10
    @7
    cN
    cmin
    oveq2
    breq2d
    cbvrabv
    eqtri
    #
    elrab2
    mpbi
    #
    simpli
    #
    nn0ge0i
    @1
    @0
    cR
    cle
    wbr
    #
    wn
    @17
    @0
    cc0
    cle
    wbr
    #
    cc0
    @0
    clt
    wbr
    @18
    wn
    @0
    cD
    cz
    wcel
    #
    cD
    cc0
    wne
    @0
    cn
    wcel
    divalglem0.2
    divalglem1.3
    cD
    nnabscl
    mp2an
    nngt0i
    cc0
    @0
    0re
    cD
    @19
    cD
    cc
    wcel
    divalglem0.2
    cD
    zcn
    ax-mp
    abscli
    #
    ltnlei
    mpbi
    @17
    cR
    cR
    @0
    cmin
    co
    #
    cle
    wbr
    #
    @18
    @17
    cR
    @6
    @21
    cle
    divalglem5.5
    @17
    cS
    cc0
    cuz
    cfv
    #
    wss
    @21
    cS
    wcel
    #
    @6
    @21
    cle
    wbr
    cS
    cn0
    @23
    cS
    @13
    cn0
    divalglem2.4
    @12
    vr
    cn0
    ssrab2
    eqsstri
    nn0uz
    sseqtri
    @17
    @21
    cn0
    wcel
    #
    cD
    cN
    @21
    cmin
    co
    #
    cdvds
    wbr
    #
    @24
    @0
    cn0
    wcel
    #
    @2
    @17
    @25
    @19
    @28
    divalglem0.2
    cD
    nn0abscl
    ax-mp
    @16
    @0
    cR
    nn0sub2
    mp3an12
    @17
    @5
    @27
    @5
    @17
    @15
    a1i
    #
    @2
    @4
    @27
    @2
    cR
    cz
    wcel
    #
    @4
    @27
    wi
    cR
    nn0z
    @30
    @4
    cD
    cN
    cR
    c1
    @0
    cmul
    co
    #
    cmin
    co
    #
    cmin
    co
    #
    cdvds
    wbr
    #
    @27
    @30
    c1
    cz
    wcel
    @4
    @34
    wi
    1z
    cD
    cR
    c1
    cN
    divalglem0.1
    divalglem0.2
    divalglem0
    mpan2
    @33
    @26
    cD
    cdvds
    @32
    @21
    cN
    cmin
    @31
    @0
    cR
    cmin
    @0
    @0
    @20
    recni
    mulid2i
    oveq2i
    oveq2i
    breq2i
    syl6ib
    syl
    imp
    syl
    @9
    @27
    vx
    @21
    cn0
    cS
    @7
    @21
    wceq
    @8
    @26
    cD
    cdvds
    @7
    @21
    cN
    cmin
    oveq2
    breq2d
    @14
    elrab2
    sylanbrc
    @21
    cS
    cc0
    infssuzle
    sylancr
    syl5eqbr
    @17
    @22
    @0
    cR
    cR
    cmin
    co
    #
    cle
    wbr
    #
    @18
    @17
    cR
    cr
    wcel
    #
    @37
    @22
    @36
    wb
    #
    @17
    @2
    @37
    @17
    @2
    @4
    @29
    simpld
    cR
    nn0re
    #
    syl
    #
    @40
    @37
    @37
    @0
    cr
    wcel
    @38
    @20
    cR
    cR
    @0
    lesub
    mp3an3
    syl2anc
    @17
    @35
    cc0
    @0
    cle
    @17
    cR
    @17
    cR
    @40
    recnd
    subidd
    breq2d
    bitrd
    mpbid
    mto
    cR
    @0
    @2
    @37
    @16
    @39
    ax-mp
    @20
    ltnlei
    mpbir
    pm3.2i
end
