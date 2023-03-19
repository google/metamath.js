include "chst.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cno.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cort.mm"
include "wceq.mm"
include "hstnmoc.mm"
include "adantlr.mm"
include "oveq2d.mm"
include "cr.mm"
include "chil.mm"
include "hstcl.mm"
include "normcl.mm"
include "syl.mm"
include "resqcld.mm"
include "adantr.mm"
include "recnd.mm"
include "choccl.mm"
include "sylan2.mm"
include "add12d.mm"
include "eqtr3d.mm"
include "adantrr.mm"
include "chj.mm"
include "ococ.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "jca.mm"
include "hstpyth.mm"
include "cc0.mm"
include "chjcl.mm"
include "anassrs.mm"
include "normge0.mm"
include "hstle1.mm"
include "1re.mm"
include "le2sq2.mm"
include "mpanr1.mm"
include "syl21anc.mm"
include "sq1.mm"
include "syl6breq.mm"
include "eqbrtrrd.mm"
include "wb.mm"
include "readdcld.mm"
include "leadd2.mm"
include "mp3an2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "leadd1.mm"
include "mp3an3.mm"
include "mpbird.mm"
include "le2sq.mm"

theorem hstle
  let cA: class A
  let cB: class B
  let cS: class S
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f


  assert |- ( ( ( S e. CHStates /\ A e. CH ) /\ ( B e. CH /\ A C_ B ) ) -> ( normh ` ( S ` A ) ) <_ ( normh ` ( S ` B ) ) )

  proof
    cS
    chst
    wcel
    #
    cA
    cch
    wcel
    #
    wa
    #
    cB
    cch
    wcel
    #
    cA
    cB
    wss
    #
    wa
    #
    wa
    #
    cA
    cS
    cfv
    #
    cno
    cfv
    #
    cB
    cS
    cfv
    #
    cno
    cfv
    #
    cle
    wbr
    #
    @8
    c2
    cexp
    co
    #
    @10
    c2
    cexp
    co
    #
    cle
    wbr
    #
    @6
    @14
    @12
    c1
    caddc
    co
    #
    @13
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @6
    @15
    @13
    @12
    cB
    cort
    cfv
    #
    cS
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    caddc
    co
    #
    @16
    cle
    @2
    @3
    @15
    @23
    wceq
    @4
    @2
    @3
    wa
    #
    @12
    @13
    @21
    caddc
    co
    #
    caddc
    co
    @15
    @23
    @24
    @25
    c1
    @12
    caddc
    @0
    @3
    @25
    c1
    wceq
    @1
    cB
    cS
    hstnmoc
    adantlr
    oveq2d
    @24
    @12
    @13
    @21
    @24
    @12
    @2
    @12
    cr
    wcel
    #
    @3
    @2
    @8
    @2
    @7
    chil
    wcel
    #
    @8
    cr
    wcel
    #
    cA
    cS
    hstcl
    #
    @7
    normcl
    syl
    #
    resqcld
    adantr
    #
    recnd
    @24
    @13
    @0
    @3
    @13
    cr
    wcel
    #
    @1
    @0
    @3
    wa
    #
    @10
    @33
    @9
    chil
    wcel
    #
    @10
    cr
    wcel
    #
    cB
    cS
    hstcl
    #
    @9
    normcl
    syl
    #
    resqcld
    adantlr
    #
    recnd
    @24
    @21
    @0
    @3
    @21
    cr
    wcel
    @1
    @33
    @20
    @33
    @19
    chil
    wcel
    #
    @20
    cr
    wcel
    @3
    @0
    @18
    cch
    wcel
    #
    @39
    cB
    choccl
    #
    @18
    cS
    hstcl
    sylan2
    @19
    normcl
    syl
    resqcld
    adantlr
    #
    recnd
    add12d
    eqtr3d
    adantrr
    @6
    @22
    c1
    cle
    wbr
    #
    @23
    @16
    cle
    wbr
    #
    @6
    cA
    @18
    chj
    co
    #
    cS
    cfv
    #
    cno
    cfv
    #
    c2
    cexp
    co
    #
    @22
    c1
    cle
    @5
    @2
    @40
    cA
    @18
    cort
    cfv
    #
    wss
    #
    wa
    @48
    @22
    wceq
    @5
    @40
    @50
    @3
    @40
    @4
    @41
    adantr
    @3
    @50
    @4
    @3
    @49
    cB
    cA
    cB
    ococ
    sseq2d
    biimpar
    jca
    cA
    @18
    cS
    hstpyth
    sylan2
    @2
    @3
    @48
    c1
    cle
    wbr
    @4
    @24
    @48
    c1
    c2
    cexp
    co
    #
    c1
    cle
    @24
    @47
    cr
    wcel
    #
    cc0
    @47
    cle
    wbr
    #
    @47
    c1
    cle
    wbr
    #
    @48
    @51
    cle
    wbr
    #
    @24
    @46
    chil
    wcel
    #
    @52
    @0
    @1
    @3
    @56
    @1
    @3
    wa
    #
    @0
    @45
    cch
    wcel
    #
    @56
    @3
    @1
    @40
    @58
    @41
    cA
    @18
    chjcl
    sylan2
    #
    @45
    cS
    hstcl
    sylan2
    anassrs
    #
    @46
    normcl
    syl
    @24
    @56
    @53
    @60
    @46
    normge0
    syl
    @0
    @1
    @3
    @54
    @57
    @0
    @58
    @54
    @59
    @45
    cS
    hstle1
    sylan2
    anassrs
    @52
    @53
    wa
    c1
    cr
    wcel
    #
    @54
    @55
    1re
    @47
    c1
    le2sq2
    mpanr1
    syl21anc
    sq1
    syl6breq
    adantrr
    eqbrtrrd
    @2
    @3
    @43
    @44
    wb
    #
    @4
    @24
    @22
    cr
    wcel
    #
    @32
    @62
    @24
    @12
    @21
    @31
    @42
    readdcld
    @38
    @63
    @61
    @32
    @62
    1re
    @22
    c1
    @13
    leadd2
    mp3an2
    syl2anc
    adantrr
    mpbid
    eqbrtrd
    @2
    @3
    @14
    @17
    wb
    #
    @4
    @24
    @26
    @32
    @64
    @31
    @38
    @26
    @32
    @61
    @64
    1re
    @12
    @13
    c1
    leadd1
    mp3an3
    syl2anc
    adantrr
    mpbird
    @2
    @3
    @11
    @14
    wb
    #
    @4
    @24
    @28
    cc0
    @8
    cle
    wbr
    #
    wa
    #
    @35
    cc0
    @10
    cle
    wbr
    #
    wa
    #
    @65
    @2
    @67
    @3
    @2
    @28
    @66
    @30
    @2
    @27
    @66
    @29
    @7
    normge0
    syl
    jca
    adantr
    @0
    @3
    @69
    @1
    @33
    @35
    @68
    @37
    @33
    @34
    @68
    @36
    @9
    normge0
    syl
    jca
    adantlr
    @8
    @10
    le2sq
    syl2anc
    adantrr
    mpbird
end
