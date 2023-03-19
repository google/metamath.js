include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cfl.mm"
include "cfv.mm"
include "cfa.mm"
include "cmul.mm"
include "cr.mm"
include "nn0readdcl.mm"
include "rehalfcld.mm"
include "flle.mm"
include "syl.mm"
include "wi.mm"
include "reflcl.mm"
include "nn0re.mm"
include "adantr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "cc0.mm"
include "nn0addcl.mm"
include "nn0ge0d.mm"
include "wb.mm"
include "halfnneg2.mm"
include "mpbid.mm"
include "flge0nn0.mm"
include "syl2anc.mm"
include "simpl.mm"
include "facwordi.mm"
include "3exp.mm"
include "sylc.mm"
include "c1.mm"
include "wceq.mm"
include "faccl.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "nnred.mm"
include "adantl.mm"
include "nnnn0d.mm"
include "jca.mm"
include "nnge1d.mm"
include "1re.mm"
include "lemul2a.mm"
include "mp3anl1.mm"
include "syl21anc.mm"
include "eqbrtrrd.mm"
include "cn.mm"
include "remulcl.mm"
include "syl2an.mm"
include "mpan2d.mm"
include "3syld.mm"
include "simpr.mm"
include "mulid2d.mm"
include "lemul1a.mm"
include "wo.mm"
include "avgle.mm"
include "mpjaod.mm"

theorem facavg
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 ) -> ( ! ` ( |_ ` ( ( M + N ) / 2 ) ) ) <_ ( ( ! ` M ) x. ( ! ` N ) ) )

  proof
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cM
    cN
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cM
    cle
    wbr
    #
    @4
    cfl
    cfv
    #
    cfa
    cfv
    #
    cM
    cfa
    cfv
    #
    cN
    cfa
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @4
    cN
    cle
    wbr
    #
    @2
    @5
    @6
    cM
    cle
    wbr
    #
    @7
    @8
    cle
    wbr
    #
    @11
    @2
    @6
    @4
    cle
    wbr
    #
    @5
    @13
    @2
    @4
    cr
    wcel
    #
    @15
    @2
    @3
    cM
    cN
    nn0readdcl
    #
    rehalfcld
    #
    @4
    flle
    syl
    #
    @2
    @6
    cr
    wcel
    #
    @16
    cM
    cr
    wcel
    #
    @15
    @5
    wa
    @13
    wi
    @2
    @16
    @20
    @18
    @4
    reflcl
    syl
    #
    @18
    @0
    @21
    @1
    cM
    nn0re
    #
    adantr
    @6
    @4
    cM
    letr
    syl3anc
    mpand
    @2
    @6
    cn0
    wcel
    #
    @0
    @13
    @14
    wi
    @2
    @16
    cc0
    @4
    cle
    wbr
    #
    @24
    @18
    @2
    cc0
    @3
    cle
    wbr
    #
    @25
    @2
    @3
    cM
    cN
    nn0addcl
    nn0ge0d
    @2
    @3
    cr
    wcel
    @26
    @25
    wb
    @17
    @3
    halfnneg2
    syl
    mpbid
    @4
    flge0nn0
    syl2anc
    #
    @0
    @1
    simpl
    @24
    @0
    @13
    @14
    @6
    cM
    facwordi
    3exp
    sylc
    @2
    @14
    @8
    @10
    cle
    wbr
    #
    @11
    @2
    @8
    c1
    cmul
    co
    #
    @8
    @10
    cle
    @0
    @29
    @8
    wceq
    @1
    @0
    @8
    @0
    @8
    cM
    faccl
    #
    nncnd
    mulid1d
    adantr
    @2
    @9
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    #
    wa
    #
    c1
    @9
    cle
    wbr
    #
    @29
    @10
    cle
    wbr
    #
    @1
    @31
    @0
    @1
    @9
    cN
    faccl
    #
    nnred
    #
    adantl
    #
    @0
    @34
    @1
    @0
    @32
    @33
    @0
    @8
    @30
    nnred
    #
    @0
    @8
    @0
    @8
    @30
    nnnn0d
    nn0ge0d
    jca
    adantr
    @1
    @35
    @0
    @1
    @9
    @37
    nnge1d
    adantl
    c1
    cr
    wcel
    #
    @31
    @34
    @35
    @36
    1re
    c1
    @9
    @8
    lemul2a
    mp3anl1
    syl21anc
    eqbrtrrd
    @2
    @7
    cr
    wcel
    #
    @32
    @10
    cr
    wcel
    #
    @14
    @28
    wa
    @11
    wi
    @2
    @7
    @2
    @24
    @7
    cn
    wcel
    @27
    @6
    faccl
    syl
    nnred
    #
    @0
    @32
    @1
    @40
    adantr
    #
    @0
    @32
    @31
    @43
    @1
    @40
    @38
    @8
    @9
    remulcl
    syl2an
    #
    @7
    @8
    @10
    letr
    syl3anc
    mpan2d
    3syld
    @2
    @12
    @6
    cN
    cle
    wbr
    #
    @7
    @9
    cle
    wbr
    #
    @11
    @2
    @15
    @12
    @47
    @19
    @2
    @20
    @16
    cN
    cr
    wcel
    #
    @15
    @12
    wa
    @47
    wi
    @22
    @18
    @1
    @49
    @0
    cN
    nn0re
    #
    adantl
    @6
    @4
    cN
    letr
    syl3anc
    mpand
    @2
    @24
    @1
    @47
    @48
    wi
    @27
    @0
    @1
    simpr
    @24
    @1
    @47
    @48
    @6
    cN
    facwordi
    3exp
    sylc
    @2
    @48
    @9
    @10
    cle
    wbr
    #
    @11
    @2
    c1
    @9
    cmul
    co
    #
    @9
    @10
    cle
    @1
    @52
    @9
    wceq
    @0
    @1
    @9
    @1
    @9
    @37
    nncnd
    mulid2d
    adantl
    @2
    @32
    @31
    cc0
    @9
    cle
    wbr
    #
    wa
    #
    c1
    @8
    cle
    wbr
    #
    @52
    @10
    cle
    wbr
    #
    @45
    @1
    @54
    @0
    @1
    @31
    @53
    @38
    @1
    @9
    @1
    @9
    @37
    nnnn0d
    nn0ge0d
    jca
    adantl
    @0
    @55
    @1
    @0
    @8
    @30
    nnge1d
    adantr
    @41
    @32
    @54
    @55
    @56
    1re
    c1
    @8
    @9
    lemul1a
    mp3anl1
    syl21anc
    eqbrtrrd
    @2
    @42
    @31
    @43
    @48
    @51
    wa
    @11
    wi
    @44
    @39
    @46
    @7
    @9
    @10
    letr
    syl3anc
    mpan2d
    3syld
    @0
    @21
    @49
    @5
    @12
    wo
    @1
    @23
    @50
    cM
    cN
    avgle
    syl2an
    mpjaod
end
