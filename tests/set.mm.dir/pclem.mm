include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "wss.mm"
include "c0.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cn0.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nn0ssz.mm"
include "sstri.mm"
include "a1i.mm"
include "0nn0.mm"
include "c1.mm"
include "cc.mm"
include "eluzelcn.mm"
include "adantr.mm"
include "exp0d.mm"
include "1dvds.mm"
include "ad2antrl.mm"
include "eqbrtrd.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "syl.mm"
include "cn.mm"
include "nnssz.mm"
include "cabs.mm"
include "clt.mm"
include "cr.mm"
include "zcn.mm"
include "abscld.mm"
include "eluzelre.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "expnbnd.mm"
include "syl3anc.mm"
include "wi.mm"
include "simprr.mm"
include "sylib.mm"
include "simprd.mm"
include "eluz2nn.mm"
include "ad2antrr.mm"
include "simpld.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "simplrl.mm"
include "simplrr.mm"
include "dvdsleabs.mm"
include "mpd.mm"
include "nnred.mm"
include "nnnn0.mm"
include "reexpcld.mm"
include "lelttr.mm"
include "mpand.mm"
include "nn0zd.mm"
include "nnz.mm"
include "ltexp2d.mm"
include "sylibrd.mm"
include "nn0red.mm"
include "nnre.mm"
include "ltle.mm"
include "syl2anc.mm"
include "syld.mm"
include "anassrs.mm"
include "ralrimdva.mm"
include "reximdva.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "3jca.mm"

theorem pclem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let vn: setvar n
  let cN: class N
  let vz: setvar z
  let cS: class S
  assume pclem.1: |- A = { n e. NN0 | ( P ^ n ) || N }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint n x
  disjoint n y
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint P n
  disjoint P x
  disjoint P y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint n z
  disjoint N z
  disjoint P z
  disjoint S x
  assert |- ( ( P e. ( ZZ>= ` 2 ) /\ ( N e. ZZ /\ N =/= 0 ) ) -> ( A C_ ZZ /\ A =/= (/) /\ E. x e. ZZ A. y e. A y <_ x ) )

  proof
    cP
    c2
    cuz
    cfv
    wcel
    #
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    wa
    #
    wa
    #
    cA
    cz
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cz
    wrex
    #
    @5
    @4
    cA
    cn0
    cz
    cA
    cP
    vn
    cv
    #
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    vn
    cn0
    crab
    cn0
    pclem.1
    @14
    vn
    cn0
    ssrab2
    eqsstri
    nn0ssz
    sstri
    a1i
    @4
    cc0
    cA
    wcel
    #
    @6
    @4
    cc0
    cn0
    wcel
    #
    cP
    cc0
    cexp
    co
    #
    cN
    cdvds
    wbr
    #
    @15
    @16
    @4
    0nn0
    a1i
    @4
    @17
    c1
    cN
    cdvds
    @4
    cP
    @0
    cP
    cc
    wcel
    @3
    c2
    cP
    eluzelcn
    adantr
    exp0d
    @1
    c1
    cN
    cdvds
    wbr
    @0
    @2
    cN
    1dvds
    ad2antrl
    eqbrtrd
    @14
    @18
    vn
    cc0
    cn0
    cA
    @12
    cc0
    wceq
    @13
    @17
    cN
    cdvds
    @12
    cc0
    cP
    cexp
    oveq2
    breq1d
    pclem.1
    elrab2
    sylanbrc
    cA
    cc0
    ne0i
    syl
    cn
    cz
    wss
    @4
    @10
    vx
    cn
    wrex
    #
    @11
    nnssz
    @4
    cN
    cabs
    cfv
    #
    cP
    @8
    cexp
    co
    #
    clt
    wbr
    #
    vx
    cn
    wrex
    #
    @19
    @4
    @20
    cr
    wcel
    #
    cP
    cr
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    @23
    @1
    @24
    @0
    @2
    @1
    cN
    cN
    zcn
    abscld
    ad2antrl
    #
    @0
    @25
    @3
    c2
    cP
    eluzelre
    #
    adantr
    @0
    @26
    @3
    @0
    cP
    cn
    wcel
    #
    @26
    cP
    eluz2b2
    simprbi
    #
    adantr
    @20
    cP
    vx
    expnbnd
    syl3anc
    @4
    @22
    @10
    vx
    cn
    @4
    @8
    cn
    wcel
    #
    wa
    @22
    @9
    vy
    cA
    @4
    @31
    @7
    cA
    wcel
    #
    @22
    @9
    wi
    @4
    @31
    @32
    wa
    #
    wa
    #
    @22
    @7
    @8
    clt
    wbr
    #
    @9
    @34
    @22
    cP
    @7
    cexp
    co
    #
    @21
    clt
    wbr
    #
    @35
    @34
    @36
    @20
    cle
    wbr
    #
    @22
    @37
    @34
    @36
    cN
    cdvds
    wbr
    #
    @38
    @34
    @7
    cn0
    wcel
    #
    @39
    @34
    @32
    @40
    @39
    wa
    @4
    @31
    @32
    simprr
    @14
    @39
    vn
    @7
    cn0
    cA
    @12
    @7
    wceq
    @13
    @36
    cN
    cdvds
    @12
    @7
    cP
    cexp
    oveq2
    breq1d
    pclem.1
    elrab2
    sylib
    #
    simprd
    @34
    @36
    cz
    wcel
    @1
    @2
    @39
    @38
    wi
    @34
    @36
    @34
    cP
    @7
    @0
    @29
    @3
    @33
    cP
    eluz2nn
    ad2antrr
    @34
    @40
    @39
    @41
    simpld
    #
    nnexpcld
    #
    nnzd
    @0
    @1
    @2
    @33
    simplrl
    @0
    @1
    @2
    @33
    simplrr
    @36
    cN
    dvdsleabs
    syl3anc
    mpd
    @34
    @36
    cr
    wcel
    @24
    @21
    cr
    wcel
    @38
    @22
    wa
    @37
    wi
    @34
    @36
    @43
    nnred
    @4
    @24
    @33
    @27
    adantr
    @34
    cP
    @8
    @0
    @25
    @3
    @33
    @28
    ad2antrr
    #
    @31
    @8
    cn0
    wcel
    @4
    @32
    @8
    nnnn0
    ad2antrl
    reexpcld
    @36
    @20
    @21
    lelttr
    syl3anc
    mpand
    @34
    cP
    @7
    @8
    @44
    @34
    @7
    @42
    nn0zd
    @31
    @8
    cz
    wcel
    @4
    @32
    @8
    nnz
    ad2antrl
    @0
    @26
    @3
    @33
    @30
    ad2antrr
    ltexp2d
    sylibrd
    @34
    @7
    cr
    wcel
    @8
    cr
    wcel
    #
    @35
    @9
    wi
    @34
    @7
    @42
    nn0red
    @31
    @45
    @4
    @32
    @8
    nnre
    ad2antrl
    @7
    @8
    ltle
    syl2anc
    syld
    anassrs
    ralrimdva
    reximdva
    mpd
    @10
    vx
    cn
    cz
    ssrexv
    mpsyl
    3jca
end
