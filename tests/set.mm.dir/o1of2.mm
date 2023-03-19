include "co1.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "cabs.mm"
include "wi.mm"
include "cdm.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "cof.mm"
include "co.mm"
include "cc.mm"
include "wf.mm"
include "o1f.mm"
include "o1bdd.mm"
include "mpdan.mm"
include "adantr.mm"
include "adantl.mm"
include "reeanv.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "inss2.mm"
include "anim12i.mm"
include "r19.26.mm"
include "sylibr.mm"
include "cif.mm"
include "prth.mm"
include "wb.mm"
include "simplrl.mm"
include "simplrr.mm"
include "o1dm.mm"
include "ad3antrrr.mm"
include "syl5ss.mm"
include "sselda.mm"
include "maxle.mm"
include "syl3anc.mm"
include "biimpd.mm"
include "sseli.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "ad3antlr.mm"
include "ralrimivva.mm"
include "ad2antlr.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "oveq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "cvv.mm"
include "wfn.mm"
include "ffn.mm"
include "syl.mm"
include "reex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "dmexg.mm"
include "eqid.mm"
include "eqidd.mm"
include "ofval.mm"
include "sylibrd.mm"
include "imim12d.mm"
include "syl5.mm"
include "ralimdva.mm"
include "off.mm"
include "ifcld.mm"
include "elo12r.mm"
include "3expia.mm"
include "syl22anc.mm"
include "syld.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mp2and.mm"

theorem o1of2
  let vx: setvar x
  let vy: setvar y
  let cR: class R
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  assume o1of2.1: |- ( ( m e. RR /\ n e. RR ) -> M e. RR )
  assume o1of2.2: |- ( ( x e. CC /\ y e. CC ) -> ( x R y ) e. CC )
  assume o1of2.3: |- ( ( ( m e. RR /\ n e. RR ) /\ ( x e. CC /\ y e. CC ) ) -> ( ( ( abs ` x ) <_ m /\ ( abs ` y ) <_ n ) -> ( abs ` ( x R y ) ) <_ M ) )

  disjoint m n
  disjoint m x
  disjoint m y
  disjoint F m
  disjoint n x
  disjoint n y
  disjoint F n
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint R m
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint M x
  disjoint M y
  disjoint a b
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint F b
  disjoint m z
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G a
  disjoint G b
  disjoint G z
  disjoint R a
  disjoint R b
  disjoint R z
  disjoint M z
  assert |- ( ( F e. O(1) /\ G e. O(1) ) -> ( F oF R G ) e. O(1) )

  proof
    cF
    co1
    wcel
    #
    cG
    co1
    wcel
    #
    wa
    #
    va
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    @4
    cF
    cfv
    #
    cabs
    cfv
    #
    vm
    cv
    #
    cle
    wbr
    #
    wi
    #
    vz
    cF
    cdm
    #
    wral
    #
    vm
    cr
    wrex
    #
    va
    cr
    wrex
    #
    vb
    cv
    #
    @4
    cle
    wbr
    #
    @4
    cG
    cfv
    #
    cabs
    cfv
    #
    vn
    cv
    #
    cle
    wbr
    #
    wi
    #
    vz
    cG
    cdm
    #
    wral
    #
    vn
    cr
    wrex
    #
    vb
    cr
    wrex
    #
    cF
    cG
    cR
    cof
    co
    #
    co1
    wcel
    #
    @0
    @14
    @1
    @0
    @11
    cc
    cF
    wf
    #
    @14
    cF
    o1f
    #
    va
    vz
    @11
    vm
    cF
    o1bdd
    mpdan
    adantr
    @1
    @25
    @0
    @1
    @22
    cc
    cG
    wf
    #
    @25
    cG
    o1f
    #
    vb
    vz
    @22
    vn
    cG
    o1bdd
    mpdan
    adantl
    @14
    @25
    wa
    @13
    @24
    wa
    #
    vb
    cr
    wrex
    va
    cr
    wrex
    @2
    @27
    @13
    @24
    va
    vb
    cr
    cr
    reeanv
    @2
    @32
    @27
    va
    vb
    cr
    cr
    @32
    @12
    @23
    wa
    #
    vn
    cr
    wrex
    vm
    cr
    wrex
    @2
    @3
    cr
    wcel
    #
    @15
    cr
    wcel
    #
    wa
    #
    wa
    #
    @27
    @12
    @23
    vm
    vn
    cr
    cr
    reeanv
    @37
    @33
    @27
    vm
    vn
    cr
    cr
    @33
    @10
    @21
    wa
    #
    vz
    @11
    @22
    cin
    #
    wral
    #
    @37
    @8
    cr
    wcel
    @19
    cr
    wcel
    wa
    #
    wa
    #
    @27
    @33
    @10
    vz
    @39
    wral
    #
    @21
    vz
    @39
    wral
    #
    wa
    @40
    @12
    @43
    @23
    @44
    @39
    @11
    wss
    @12
    @43
    wi
    @11
    @22
    inss1
    #
    @10
    vz
    @39
    @11
    ssralv
    ax-mp
    @39
    @22
    wss
    @23
    @44
    wi
    @11
    @22
    inss2
    #
    @21
    vz
    @39
    @22
    ssralv
    ax-mp
    anim12i
    @10
    @21
    vz
    @39
    r19.26
    sylibr
    @42
    @40
    @3
    @15
    cle
    wbr
    #
    @15
    @3
    cif
    #
    @4
    cle
    wbr
    #
    @4
    @26
    cfv
    #
    cabs
    cfv
    #
    cM
    cle
    wbr
    #
    wi
    #
    vz
    @39
    wral
    #
    @27
    @42
    @38
    @53
    vz
    @39
    @38
    @5
    @16
    wa
    #
    @9
    @20
    wa
    #
    wi
    @42
    @4
    @39
    wcel
    #
    wa
    #
    @53
    @5
    @9
    @16
    @20
    prth
    @58
    @49
    @55
    @56
    @52
    @58
    @49
    @55
    @58
    @34
    @35
    @4
    cr
    wcel
    @49
    @55
    wb
    @42
    @34
    @57
    @2
    @34
    @35
    @41
    simplrl
    #
    adantr
    @42
    @35
    @57
    @2
    @34
    @35
    @41
    simplrr
    #
    adantr
    @42
    @39
    cr
    @4
    @42
    @39
    @11
    cr
    @45
    @0
    @11
    cr
    wss
    #
    @1
    @36
    @41
    cF
    o1dm
    ad3antrrr
    #
    syl5ss
    #
    sselda
    @3
    @15
    @4
    maxle
    syl3anc
    biimpd
    @58
    @56
    @6
    @17
    cR
    co
    #
    cabs
    cfv
    #
    cM
    cle
    wbr
    #
    @52
    @58
    @6
    cc
    wcel
    #
    @17
    cc
    wcel
    #
    vx
    cv
    #
    cabs
    cfv
    #
    @8
    cle
    wbr
    #
    vy
    cv
    #
    cabs
    cfv
    #
    @19
    cle
    wbr
    #
    wa
    #
    @69
    @72
    cR
    co
    #
    cabs
    cfv
    #
    cM
    cle
    wbr
    #
    wi
    #
    vy
    cc
    wral
    vx
    cc
    wral
    #
    @56
    @66
    wi
    #
    @42
    @28
    @4
    @11
    wcel
    #
    @67
    @57
    @0
    @28
    @1
    @36
    @41
    @29
    ad3antrrr
    #
    @39
    @11
    @4
    @45
    sseli
    @11
    cc
    @4
    cF
    ffvelrn
    syl2an
    @42
    @30
    @4
    @22
    wcel
    #
    @68
    @57
    @1
    @30
    @0
    @36
    @41
    @31
    ad3antlr
    #
    @39
    @22
    @4
    @46
    sseli
    @22
    cc
    @4
    cG
    ffvelrn
    syl2an
    @41
    @80
    @37
    @57
    @41
    @79
    vx
    vy
    cc
    cc
    o1of2.3
    ralrimivva
    ad2antlr
    @79
    @81
    @9
    @74
    wa
    #
    @6
    @72
    cR
    co
    #
    cabs
    cfv
    #
    cM
    cle
    wbr
    #
    wi
    vx
    vy
    @6
    @17
    cc
    cc
    @69
    @6
    wceq
    #
    @75
    @86
    @78
    @89
    @90
    @71
    @9
    @74
    @90
    @70
    @7
    @8
    cle
    @69
    @6
    cabs
    fveq2
    breq1d
    anbi1d
    @90
    @77
    @88
    cM
    cle
    @90
    @76
    @87
    cabs
    @69
    @6
    @72
    cR
    oveq1
    fveq2d
    breq1d
    imbi12d
    @72
    @17
    wceq
    #
    @86
    @56
    @89
    @66
    @91
    @74
    @20
    @9
    @91
    @73
    @18
    @19
    cle
    @72
    @17
    cabs
    fveq2
    breq1d
    anbi2d
    @91
    @88
    @65
    cM
    cle
    @91
    @87
    @64
    cabs
    @72
    @17
    @6
    cR
    oveq2
    fveq2d
    breq1d
    imbi12d
    rspc2va
    syl21anc
    @58
    @51
    @65
    cM
    cle
    @58
    @50
    @64
    cabs
    @42
    @11
    @22
    @6
    @17
    cR
    @39
    cF
    cG
    cvv
    cvv
    @4
    @42
    @28
    cF
    @11
    wfn
    @83
    @11
    cc
    cF
    ffn
    syl
    @42
    @30
    cG
    @22
    wfn
    @85
    @22
    cc
    cG
    ffn
    syl
    @42
    @61
    cr
    cvv
    wcel
    @11
    cvv
    wcel
    @62
    reex
    @11
    cr
    cvv
    ssexg
    sylancl
    #
    @1
    @22
    cvv
    wcel
    @0
    @36
    @41
    cG
    co1
    dmexg
    ad3antlr
    #
    @39
    eqid
    #
    @42
    @82
    wa
    @6
    eqidd
    @42
    @84
    wa
    @17
    eqidd
    ofval
    fveq2d
    breq1d
    sylibrd
    imim12d
    syl5
    ralimdva
    @42
    @39
    cc
    @26
    wf
    #
    @39
    cr
    wss
    #
    @48
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    @54
    @27
    wi
    @42
    vx
    vy
    @11
    @22
    @39
    cR
    cc
    cc
    cc
    cF
    cG
    cvv
    cvv
    @69
    cc
    wcel
    @72
    cc
    wcel
    wa
    @76
    cc
    wcel
    @42
    o1of2.2
    adantl
    @83
    @85
    @92
    @93
    @94
    off
    @63
    @42
    @47
    @15
    @3
    cr
    @60
    @59
    ifcld
    @41
    @98
    @37
    o1of2.1
    adantl
    @95
    @96
    wa
    @97
    @98
    wa
    @54
    @27
    vz
    @39
    @48
    @26
    cM
    elo12r
    3expia
    syl22anc
    syld
    syl5
    rexlimdvva
    syl5bir
    rexlimdvva
    syl5bir
    mp2and
end
