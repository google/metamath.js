include "cabl.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "csubg.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "ssrab2.mm"
include "a1i.mm"
include "c0g.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "adantr.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "c1.mm"
include "wceq.mm"
include "od1.mm"
include "1dvds.mm"
include "adantl.mm"
include "eqbrtrd.mm"
include "fveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "simprl.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "cmg.mm"
include "simplll.mm"
include "simpllr.mm"
include "mulgdi.mm"
include "syl13anc.mm"
include "simprr.mm"
include "wb.mm"
include "oddvds.mm"
include "mpbid.mm"
include "oveq12d.mm"
include "grplid.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "mpbird.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "grpinvcl.mm"
include "odinv.mm"
include "jca.mm"
include "w3a.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem oddvdssubg
  let vx: setvar x
  let cB: class B
  let cG: class G
  let cN: class N
  let cO: class O
  let vy: setvar y
  let vz: setvar z
  assume torsubg.1: |- O = ( od ` G )
  assume oddvdssubg.1: |- B = ( Base ` G )

  disjoint B x
  disjoint G x
  disjoint N x
  disjoint O x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G y
  disjoint G z
  disjoint N y
  disjoint N z
  disjoint O y
  disjoint O z
  assert |- ( ( G e. Abel /\ N e. ZZ ) -> { x e. B | ( O ` x ) || N } e. ( SubGrp ` G ) )

  proof
    cG
    cabl
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    vx
    cv
    #
    cO
    cfv
    #
    cN
    cdvds
    wbr
    #
    vx
    cB
    crab
    #
    cG
    csubg
    cfv
    wcel
    #
    @6
    cB
    wss
    #
    @6
    c0
    wne
    #
    vy
    cv
    #
    vz
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @6
    wcel
    #
    vz
    @6
    wral
    #
    @10
    cG
    cminusg
    cfv
    #
    cfv
    #
    @6
    wcel
    #
    wa
    #
    vy
    @6
    wral
    #
    @8
    @2
    @5
    vx
    cB
    ssrab2
    a1i
    @2
    cG
    c0g
    cfv
    #
    @6
    wcel
    #
    @9
    @2
    @21
    cB
    wcel
    #
    @21
    cO
    cfv
    #
    cN
    cdvds
    wbr
    #
    @22
    @2
    cG
    cgrp
    wcel
    #
    @23
    @0
    @26
    @1
    cG
    ablgrp
    adantr
    #
    cB
    cG
    @21
    oddvdssubg.1
    @21
    eqid
    #
    grpidcl
    #
    syl
    @2
    @24
    c1
    cN
    cdvds
    @2
    @26
    @24
    c1
    wceq
    @27
    cG
    cO
    @21
    torsubg.1
    @28
    od1
    syl
    @1
    c1
    cN
    cdvds
    wbr
    @0
    cN
    1dvds
    adantl
    eqbrtrd
    @5
    @25
    vx
    @21
    cB
    @3
    @21
    wceq
    @4
    @24
    cN
    cdvds
    @3
    @21
    cO
    fveq2
    breq1d
    elrab
    sylanbrc
    @6
    @21
    ne0i
    syl
    @2
    @19
    vy
    @6
    @10
    @6
    wcel
    @2
    @10
    cB
    wcel
    #
    @10
    cO
    cfv
    #
    cN
    cdvds
    wbr
    #
    wa
    #
    @19
    @5
    @32
    vx
    @10
    cB
    @3
    @10
    wceq
    @4
    @31
    cN
    cdvds
    @3
    @10
    cO
    fveq2
    breq1d
    elrab
    @2
    @33
    wa
    #
    @15
    @18
    @34
    @14
    vz
    @6
    @11
    @6
    wcel
    @34
    @11
    cB
    wcel
    #
    @11
    cO
    cfv
    #
    cN
    cdvds
    wbr
    #
    wa
    #
    @14
    @5
    @37
    vx
    @11
    cB
    @3
    @11
    wceq
    @4
    @36
    cN
    cdvds
    @3
    @11
    cO
    fveq2
    breq1d
    elrab
    @34
    @38
    wa
    #
    @13
    cB
    wcel
    #
    @13
    cO
    cfv
    #
    cN
    cdvds
    wbr
    #
    @14
    @39
    @26
    @30
    @35
    @40
    @34
    @26
    @38
    @2
    @26
    @33
    @27
    adantr
    #
    adantr
    #
    @34
    @30
    @38
    @2
    @30
    @32
    simprl
    #
    adantr
    #
    @34
    @35
    @37
    simprl
    #
    cB
    @12
    cG
    @10
    @11
    oddvdssubg.1
    @12
    eqid
    #
    grpcl
    syl3anc
    #
    @39
    @42
    cN
    @13
    cG
    cmg
    cfv
    #
    co
    #
    @21
    wceq
    #
    @39
    @51
    cN
    @10
    @50
    co
    #
    cN
    @11
    @50
    co
    #
    @12
    co
    #
    @21
    @21
    @12
    co
    #
    @21
    @39
    @0
    @1
    @30
    @35
    @51
    @55
    wceq
    @0
    @1
    @33
    @38
    simplll
    @0
    @1
    @33
    @38
    simpllr
    #
    @46
    @47
    cB
    @12
    @50
    cG
    cN
    @10
    @11
    oddvdssubg.1
    @50
    eqid
    #
    @48
    mulgdi
    syl13anc
    @39
    @53
    @21
    @54
    @21
    @12
    @39
    @32
    @53
    @21
    wceq
    #
    @34
    @32
    @38
    @2
    @30
    @32
    simprr
    #
    adantr
    @39
    @26
    @30
    @1
    @32
    @59
    wb
    @44
    @46
    @57
    @10
    @50
    cG
    cN
    cO
    cB
    @21
    oddvdssubg.1
    torsubg.1
    @58
    @28
    oddvds
    syl3anc
    mpbid
    @39
    @37
    @54
    @21
    wceq
    #
    @34
    @35
    @37
    simprr
    @39
    @26
    @35
    @1
    @37
    @61
    wb
    @44
    @47
    @57
    @11
    @50
    cG
    cN
    cO
    cB
    @21
    oddvdssubg.1
    torsubg.1
    @58
    @28
    oddvds
    syl3anc
    mpbid
    oveq12d
    @39
    @26
    @23
    @56
    @21
    wceq
    @44
    @39
    @26
    @23
    @44
    @29
    syl
    cB
    @12
    cG
    @21
    @21
    oddvdssubg.1
    @48
    @28
    grplid
    syl2anc
    3eqtrd
    @39
    @26
    @40
    @1
    @42
    @52
    wb
    @44
    @49
    @57
    @13
    @50
    cG
    cN
    cO
    cB
    @21
    oddvdssubg.1
    torsubg.1
    @58
    @28
    oddvds
    syl3anc
    mpbird
    @5
    @42
    vx
    @13
    cB
    @3
    @13
    wceq
    @4
    @41
    cN
    cdvds
    @3
    @13
    cO
    fveq2
    breq1d
    elrab
    sylanbrc
    sylan2b
    ralrimiva
    @34
    @17
    cB
    wcel
    #
    @17
    cO
    cfv
    #
    cN
    cdvds
    wbr
    #
    @18
    @34
    @26
    @30
    @62
    @43
    @45
    cB
    cG
    @16
    @10
    oddvdssubg.1
    @16
    eqid
    #
    grpinvcl
    syl2anc
    @34
    @63
    @31
    cN
    cdvds
    @34
    @26
    @30
    @63
    @31
    wceq
    @43
    @45
    @10
    cG
    @16
    cO
    cB
    torsubg.1
    @65
    oddvdssubg.1
    odinv
    syl2anc
    @60
    eqbrtrd
    @5
    @64
    vx
    @17
    cB
    @3
    @17
    wceq
    @4
    @63
    cN
    cdvds
    @3
    @17
    cO
    fveq2
    breq1d
    elrab
    sylanbrc
    jca
    sylan2b
    ralrimiva
    @2
    @26
    @7
    @8
    @9
    @20
    w3a
    wb
    @27
    vy
    vz
    cB
    @12
    @6
    cG
    @16
    oddvdssubg.1
    @48
    @65
    issubg2
    syl
    mpbir3and
end
