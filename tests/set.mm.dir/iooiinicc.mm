include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "caddc.mm"
include "cioo.mm"
include "ciin.mm"
include "cicc.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cr.mm"
include "adantr.mm"
include "wrex.mm"
include "1nn.mm"
include "ioossre.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "iinss.mm"
include "ax-mp.mm"
include "a1i.mm"
include "simpr.mm"
include "sseldd.mm"
include "cle.mm"
include "wbr.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfii1.mm"
include "nfel.mm"
include "nfan.mm"
include "simpll.mm"
include "iinss2.mm"
include "adantl.mm"
include "simpl.mm"
include "adantll.mm"
include "adantlr.mm"
include "elioore.mm"
include "nnrecre.mm"
include "readdcld.mm"
include "clt.mm"
include "cxr.mm"
include "resubcld.mm"
include "rexrd.mm"
include "simplr.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "ltsubaddd.mm"
include "mpbid.mm"
include "ltled.mm"
include "syl21anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "xrralrecnnle.mm"
include "mpbird.mm"
include "iooltub.mm"
include "eliccd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "crp.mm"
include "1rp.mm"
include "nnrp.mm"
include "rpdivcld.mm"
include "ltsubrpd.mm"
include "ltaddrpd.mm"
include "iccssioo.mm"
include "syl22anc.mm"
include "ssiin.mm"
include "eqssd.mm"

theorem iooiinicc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vx: setvar x
  assume iooiinicc.a: |- ( ph -> A e. RR )
  assume iooiinicc.b: |- ( ph -> B e. RR )

  disjoint A n
  disjoint B n
  disjoint n ph
  disjoint A x
  disjoint n x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> |^|_ n e. NN ( ( A - ( 1 / n ) ) (,) ( B + ( 1 / n ) ) ) = ( A [,] B ) )

  proof
    wph
    vn
    cn
    cA
    c1
    vn
    cv
    #
    cdiv
    co
    #
    cmin
    co
    #
    cB
    @1
    caddc
    co
    #
    cioo
    co
    #
    ciin
    #
    cA
    cB
    cicc
    co
    #
    wph
    vx
    cv
    #
    @6
    wcel
    #
    vx
    @5
    wral
    @5
    @6
    wss
    wph
    @8
    vx
    @5
    wph
    @7
    @5
    wcel
    #
    wa
    #
    cA
    cB
    @7
    wph
    cA
    cr
    wcel
    #
    @9
    iooiinicc.a
    adantr
    #
    wph
    cB
    cr
    wcel
    #
    @9
    iooiinicc.b
    adantr
    #
    @10
    @5
    cr
    @7
    @5
    cr
    wss
    #
    @10
    @4
    cr
    wss
    #
    vn
    cn
    wrex
    #
    @15
    c1
    cn
    wcel
    cA
    c1
    c1
    cdiv
    co
    #
    cmin
    co
    #
    cB
    @18
    caddc
    co
    #
    cioo
    co
    #
    cr
    wss
    #
    @17
    1nn
    @19
    @20
    ioossre
    @16
    @22
    vn
    c1
    cn
    @0
    c1
    wceq
    #
    @4
    @21
    cr
    @23
    @2
    @19
    @3
    @20
    cioo
    @23
    @1
    @18
    cA
    cmin
    @0
    c1
    c1
    cdiv
    oveq2
    #
    oveq2d
    @23
    @1
    @18
    cB
    caddc
    @24
    oveq2d
    oveq12d
    sseq1d
    rspcev
    mp2an
    vn
    cn
    @4
    cr
    iinss
    ax-mp
    a1i
    wph
    @9
    simpr
    sseldd
    #
    @10
    cA
    @7
    cle
    wbr
    cA
    @7
    @1
    caddc
    co
    #
    cle
    wbr
    #
    vn
    cn
    wral
    @10
    @27
    vn
    cn
    wph
    @9
    vn
    wph
    vn
    nfv
    vn
    @7
    @5
    vn
    @7
    nfcv
    vn
    cn
    @4
    nfii1
    nfel
    nfan
    #
    @10
    @0
    cn
    wcel
    #
    @27
    @10
    @29
    wa
    #
    wph
    @7
    @4
    wcel
    #
    @29
    @27
    wph
    @9
    @29
    simpll
    #
    @9
    @29
    @31
    wph
    @9
    @29
    wa
    @5
    @4
    @7
    @29
    @5
    @4
    wss
    @9
    vn
    cn
    @4
    iinss2
    adantl
    @9
    @29
    simpl
    sseldd
    adantll
    #
    @10
    @29
    simpr
    #
    wph
    @31
    wa
    #
    @29
    wa
    #
    cA
    @26
    wph
    @29
    @11
    @31
    wph
    @11
    @29
    iooiinicc.a
    adantr
    #
    adantlr
    #
    @31
    @29
    @26
    cr
    wcel
    wph
    @31
    @29
    wa
    @7
    @1
    @31
    @7
    cr
    wcel
    #
    @29
    @7
    @2
    @3
    elioore
    adantr
    #
    @29
    @1
    cr
    wcel
    #
    @31
    @0
    nnrecre
    #
    adantl
    readdcld
    adantll
    @36
    @2
    @7
    clt
    wbr
    #
    cA
    @26
    clt
    wbr
    @36
    @2
    cxr
    wcel
    #
    @3
    cxr
    wcel
    #
    @31
    @43
    wph
    @29
    @44
    @31
    wph
    @29
    wa
    #
    @2
    @46
    cA
    @1
    @37
    @29
    @41
    wph
    @42
    adantl
    #
    resubcld
    rexrd
    #
    adantlr
    #
    wph
    @29
    @45
    @31
    @46
    @3
    @46
    cB
    @1
    wph
    @13
    @29
    iooiinicc.b
    adantr
    #
    @47
    readdcld
    #
    rexrd
    #
    adantlr
    #
    wph
    @31
    @29
    simplr
    #
    @2
    @3
    @7
    ioogtlb
    syl3anc
    @36
    cA
    @1
    @7
    @38
    @29
    @41
    @35
    @42
    adantl
    @31
    @29
    @39
    wph
    @40
    adantll
    #
    ltsubaddd
    mpbid
    ltled
    syl21anc
    ex
    ralrimi
    @10
    cA
    @7
    vn
    @28
    @10
    cA
    @12
    rexrd
    @25
    xrralrecnnle
    mpbird
    @10
    @7
    cB
    cle
    wbr
    @7
    @3
    cle
    wbr
    #
    vn
    cn
    wral
    @10
    @56
    vn
    cn
    @28
    @10
    @29
    @56
    @30
    wph
    @31
    @29
    @56
    @32
    @33
    @34
    @36
    @7
    @3
    @55
    wph
    @29
    @3
    cr
    wcel
    @31
    @51
    adantlr
    @36
    @44
    @45
    @31
    @7
    @3
    clt
    wbr
    @49
    @53
    @54
    @2
    @3
    @7
    iooltub
    syl3anc
    ltled
    syl21anc
    ex
    ralrimi
    @10
    @7
    cB
    vn
    @28
    @10
    @7
    @25
    rexrd
    @14
    xrralrecnnle
    mpbird
    eliccd
    ralrimiva
    vx
    @5
    @6
    dfss3
    sylibr
    wph
    @6
    @4
    wss
    #
    vn
    cn
    wral
    @6
    @5
    wss
    wph
    @57
    vn
    cn
    @46
    @44
    @45
    @2
    cA
    clt
    wbr
    cB
    @3
    clt
    wbr
    @57
    @48
    @52
    @46
    cA
    @1
    @37
    @29
    @1
    crp
    wcel
    wph
    @29
    c1
    @0
    c1
    crp
    wcel
    @29
    1rp
    a1i
    @0
    nnrp
    rpdivcld
    adantl
    #
    ltsubrpd
    @46
    cB
    @1
    @50
    @58
    ltaddrpd
    @2
    @3
    cA
    cB
    iccssioo
    syl22anc
    ralrimiva
    vn
    cn
    @4
    @6
    ssiin
    sylibr
    eqssd
end
