include "cv.mm"
include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cn.mm"
include "wss.mm"
include "wf.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cdvds.mm"
include "wbr.mm"
include "cprod.mm"
include "wi.mm"
include "cun.mm"
include "cmul.mm"
include "nfv.mm"
include "nfcv.mm"
include "simpll.mm"
include "unss.mm"
include "vex.mm"
include "snss.mm"
include "biimpri.mm"
include "adantl.mm"
include "sylbir.mm"
include "adantr.mm"
include "simplr.mm"
include "simprrr.mm"
include "simpl.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "nncnd.mm"
include "fveq2.mm"
include "fprodsplitsn.mm"
include "ad2ant2r.mm"
include "cz.mm"
include "w3a.mm"
include "simprl.mm"
include "simprr.mm"
include "fprodnncl.mm"
include "ex.mm"
include "com12.mm"
include "imp.mm"
include "nnzd.mm"
include "nnz.mm"
include "3jca.mm"
include "impcom.mm"
include "ralunb.mm"
include "simplbi.mm"
include "wo.mm"
include "vsnid.mm"
include "olci.mm"
include "elun.mm"
include "mpbir.mm"
include "a1i.mm"
include "snssi.mm"
include "ssneld.mm"
include "eldifd.mm"
include "oveq2d.mm"
include "eqeq1d.mm"
include "rspcv.mm"
include "syl.mm"
include "ralimdva.mm"
include "syl5.mm"
include "wnel.mm"
include "raldifb.mm"
include "biimpi.mm"
include "sylbi.mm"
include "ralimi.mm"
include "coprmprod.mm"
include "syl31anc.mm"
include "adantrd.mm"
include "expimpd.mm"
include "ralbii.mm"
include "anbi1i.mm"
include "simprrl.mm"
include "jca32.mm"
include "pm2.27.mm"
include "syl2anc.mm"
include "exp31.mm"
include "com24.mm"
include "syl5bi.mm"
include "syl2ani.mm"
include "impr.mm"
include "breq1d.mm"
include "ax-mp.mm"
include "coprmdvds2.mm"
include "syl22anc.mm"
include "eqbrtrd.mm"

theorem coprmproddvdslem
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cK: class K
  let vx: setvar x
  let cM: class M

  disjoint F m
  disjoint F n
  disjoint m n
  disjoint K m
  disjoint K y
  disjoint K z
  disjoint m y
  disjoint m z
  disjoint y z
  disjoint n y
  disjoint n z
  disjoint K x
  disjoint m x
  disjoint x y
  disjoint x z
  disjoint M m
  disjoint M n
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint n x
  assert |- ( ( y e. Fin /\ -. z e. y ) -> ( ( ( ( y C_ NN /\ ( K e. NN /\ F : NN --> NN ) ) /\ ( A. m e. y A. n e. ( y \ { m } ) ( ( F ` m ) gcd ( F ` n ) ) = 1 /\ A. m e. y ( F ` m ) || K ) ) -> prod_ m e. y ( F ` m ) || K ) -> ( ( ( ( y u. { z } ) C_ NN /\ ( K e. NN /\ F : NN --> NN ) ) /\ ( A. m e. ( y u. { z } ) A. n e. ( ( y u. { z } ) \ { m } ) ( ( F ` m ) gcd ( F ` n ) ) = 1 /\ A. m e. ( y u. { z } ) ( F ` m ) || K ) ) -> prod_ m e. ( y u. { z } ) ( F ` m ) || K ) ) )

  proof
    vy
    cv
    #
    cfn
    wcel
    #
    vz
    cv
    #
    @0
    wcel
    #
    wn
    #
    wa
    #
    @0
    cn
    wss
    #
    cK
    cn
    wcel
    #
    cn
    cn
    cF
    wf
    #
    wa
    #
    wa
    #
    vm
    cv
    #
    cF
    cfv
    #
    vn
    cv
    #
    cF
    cfv
    #
    cgcd
    co
    #
    c1
    wceq
    #
    vn
    @0
    @11
    csn
    #
    cdif
    wral
    #
    vm
    @0
    wral
    #
    @12
    cK
    cdvds
    wbr
    #
    vm
    @0
    wral
    #
    wa
    #
    wa
    #
    @0
    @12
    vm
    cprod
    #
    cK
    cdvds
    wbr
    #
    wi
    #
    @0
    @2
    csn
    #
    cun
    #
    cn
    wss
    #
    @9
    wa
    #
    @16
    vn
    @28
    @17
    cdif
    #
    wral
    #
    vm
    @28
    wral
    #
    @20
    vm
    @28
    wral
    #
    wa
    #
    wa
    #
    @28
    @12
    vm
    cprod
    #
    cK
    cdvds
    wbr
    @5
    @26
    wa
    #
    @36
    wa
    #
    @37
    @24
    @2
    cF
    cfv
    #
    cmul
    co
    #
    cK
    cdvds
    @5
    @30
    @37
    @41
    wceq
    @26
    @35
    @5
    @30
    wa
    #
    @0
    @2
    @12
    @40
    vm
    cn
    @42
    vm
    nfv
    vm
    @40
    nfcv
    @1
    @4
    @30
    simpll
    #
    @30
    @2
    cn
    wcel
    #
    @5
    @29
    @44
    @9
    @29
    @6
    @27
    cn
    wss
    #
    wa
    #
    @44
    @0
    @27
    cn
    unss
    #
    @45
    @44
    @6
    @44
    @45
    @2
    cn
    vz
    vex
    snss
    biimpri
    adantl
    sylbir
    #
    adantr
    #
    adantl
    #
    @1
    @4
    @30
    simplr
    @42
    @11
    @0
    wcel
    #
    wa
    #
    @12
    @52
    cn
    cn
    @11
    cF
    @42
    @8
    @51
    @5
    @29
    @7
    @8
    simprrr
    #
    adantr
    @42
    @0
    cn
    @11
    @30
    @6
    @5
    @29
    @6
    @9
    @29
    @46
    @6
    @47
    @6
    @45
    simpl
    sylbir
    adantr
    #
    adantl
    #
    sselda
    ffvelrnd
    nncnd
    @11
    @2
    cF
    fveq2
    #
    @42
    @40
    @42
    cn
    cn
    @2
    cF
    @53
    @50
    ffvelrnd
    nncnd
    fprodsplitsn
    ad2ant2r
    @39
    @24
    cz
    wcel
    #
    @40
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    w3a
    #
    @24
    @40
    cgcd
    co
    c1
    wceq
    #
    @25
    @40
    cK
    cdvds
    wbr
    #
    @41
    cK
    cdvds
    wbr
    #
    @39
    @57
    @58
    @59
    @39
    @24
    @38
    @36
    @24
    cn
    wcel
    #
    @5
    @36
    @64
    wi
    @26
    @36
    @5
    @64
    @30
    @5
    @64
    wi
    @35
    @30
    @5
    @64
    @30
    @5
    wa
    #
    @0
    @12
    vm
    @30
    @1
    @4
    simprl
    @65
    @51
    wa
    cn
    cn
    @11
    cF
    @65
    @8
    @51
    @30
    @8
    @5
    @29
    @7
    @8
    simprr
    #
    adantr
    adantr
    @65
    @0
    cn
    @11
    @30
    @6
    @5
    @54
    adantr
    sselda
    ffvelrnd
    fprodnncl
    ex
    adantr
    com12
    adantr
    imp
    nnzd
    @36
    @58
    @38
    @30
    @58
    @35
    @30
    @40
    @30
    cn
    cn
    @2
    cF
    @66
    @49
    ffvelrnd
    nnzd
    adantr
    adantl
    @36
    @59
    @38
    @30
    @59
    @35
    @9
    @59
    @29
    @7
    @59
    @8
    cK
    nnz
    adantr
    adantl
    adantr
    adantl
    3jca
    @38
    @36
    @61
    @5
    @36
    @61
    wi
    @26
    @5
    @30
    @35
    @61
    @42
    @33
    @61
    @34
    @42
    @33
    @61
    @42
    @33
    wa
    @1
    @6
    @40
    cn
    wcel
    #
    w3a
    #
    @8
    @12
    @40
    cgcd
    co
    #
    c1
    wceq
    #
    vm
    @0
    wral
    #
    @19
    @61
    @42
    @68
    @33
    @42
    @1
    @6
    @67
    @43
    @55
    @30
    @67
    @5
    @9
    @29
    @67
    @8
    @29
    @67
    wi
    @7
    @8
    @29
    @67
    @8
    @29
    wa
    cn
    cn
    @2
    cF
    @8
    @29
    simpl
    @29
    @44
    @8
    @48
    adantl
    ffvelrnd
    ex
    adantl
    impcom
    adantl
    3jca
    adantr
    @42
    @8
    @33
    @53
    adantr
    @42
    @33
    @71
    @33
    @32
    vm
    @0
    wral
    #
    @42
    @71
    @33
    @72
    @32
    vm
    @27
    wral
    #
    @32
    vm
    @0
    @27
    ralunb
    #
    simplbi
    @42
    @32
    @70
    vm
    @0
    @52
    @2
    @31
    wcel
    @32
    @70
    wi
    @52
    @2
    @28
    @17
    @2
    @28
    wcel
    #
    @52
    @75
    @3
    @2
    @27
    wcel
    #
    wo
    @76
    @3
    vz
    vsnid
    olci
    @2
    @0
    @27
    elun
    mpbir
    #
    a1i
    @42
    @51
    @2
    @17
    wcel
    wn
    #
    @5
    @51
    @78
    wi
    #
    @30
    @4
    @79
    @1
    @51
    @4
    @78
    @51
    @17
    @0
    @2
    @11
    @0
    snssi
    ssneld
    com12
    adantl
    adantr
    imp
    eldifd
    @16
    @70
    vn
    @2
    @31
    @13
    @2
    wceq
    #
    @15
    @69
    c1
    @80
    @14
    @40
    @12
    cgcd
    @13
    @2
    cF
    fveq2
    oveq2d
    eqeq1d
    rspcv
    syl
    ralimdva
    syl5
    imp
    @33
    @19
    @42
    @33
    @72
    @73
    wa
    #
    @19
    @74
    @72
    @19
    @73
    @32
    @18
    vm
    @0
    @32
    @13
    @17
    wnel
    @16
    wi
    #
    vn
    @28
    wral
    #
    @18
    @16
    vn
    @28
    @17
    raldifb
    #
    @83
    @82
    vn
    @0
    wral
    #
    @82
    vn
    @27
    wral
    #
    wa
    @18
    @82
    vn
    @0
    @27
    ralunb
    #
    @85
    @18
    @86
    @85
    @18
    @16
    vn
    @0
    @17
    raldifb
    #
    biimpi
    adantr
    sylbi
    sylbir
    ralimi
    adantr
    sylbi
    adantl
    @68
    @8
    @71
    w3a
    @19
    @61
    vm
    vn
    cF
    @0
    @40
    coprmprod
    imp
    syl31anc
    ex
    adantrd
    expimpd
    adantr
    imp
    @38
    @30
    @35
    @25
    @33
    @38
    @30
    wa
    #
    @85
    vm
    @0
    wral
    #
    @21
    @25
    @34
    @33
    @81
    @90
    @74
    @72
    @90
    @73
    @32
    @85
    vm
    @0
    @32
    @83
    @85
    @84
    @83
    @85
    @86
    @87
    simplbi
    sylbir
    ralimi
    adantr
    sylbi
    @34
    @21
    @20
    vm
    @27
    wral
    @20
    vm
    @0
    @27
    ralunb
    simplbi
    @90
    @21
    wa
    @22
    @89
    @25
    @90
    @19
    @21
    @85
    @18
    vm
    @0
    @88
    ralbii
    anbi1i
    @38
    @30
    @22
    @25
    wi
    #
    @5
    @26
    @30
    @91
    wi
    @5
    @22
    @30
    @26
    @25
    @5
    @22
    @30
    @26
    @25
    wi
    #
    @5
    @22
    wa
    #
    @30
    wa
    #
    @10
    @22
    @92
    @94
    @6
    @7
    @8
    @30
    @6
    @93
    @54
    adantl
    @93
    @29
    @7
    @8
    simprrl
    @93
    @29
    @7
    @8
    simprrr
    jca32
    @5
    @22
    @30
    simplr
    @23
    @25
    pm2.27
    syl2anc
    exp31
    com24
    imp
    imp
    syl5bi
    syl2ani
    impr
    @36
    @62
    @38
    @35
    @62
    @30
    @34
    @62
    @33
    @75
    @34
    @62
    wi
    @77
    @20
    @62
    vm
    @2
    @28
    @11
    @2
    wceq
    @12
    @40
    cK
    cdvds
    @56
    breq1d
    rspcv
    ax-mp
    adantl
    adantl
    adantl
    @60
    @61
    wa
    @25
    @62
    wa
    @63
    cK
    @24
    @40
    coprmdvds2
    imp
    syl22anc
    eqbrtrd
    exp31
end
