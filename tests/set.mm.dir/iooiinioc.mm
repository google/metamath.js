include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cioo.mm"
include "ciin.mm"
include "cioc.mm"
include "wcel.mm"
include "wral.mm"
include "wss.mm"
include "wa.mm"
include "cxr.mm"
include "adantr.mm"
include "cr.mm"
include "rexrd.mm"
include "wrex.mm"
include "1nn.mm"
include "ioossre.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "mp2an.mm"
include "iinss.mm"
include "ax-mp.mm"
include "a1i.mm"
include "simpr.mm"
include "sseldd.mm"
include "clt.mm"
include "wbr.mm"
include "1red.mm"
include "cc0.mm"
include "wne.mm"
include "ax-1ne0.mm"
include "redivcld.mm"
include "readdcld.mm"
include "id.mm"
include "eleq2d.mm"
include "eliind.mm"
include "adantl.mm"
include "ioogtlb.mm"
include "syl3anc.mm"
include "cle.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfii1.mm"
include "nfel.mm"
include "nfan.mm"
include "simpll.mm"
include "iinss2.mm"
include "simpl.mm"
include "adantll.mm"
include "elioore.mm"
include "nnrecre.mm"
include "adantlr.mm"
include "simplr.mm"
include "iooltub.mm"
include "ltled.mm"
include "syl21anc.mm"
include "ex.mm"
include "ralrimi.mm"
include "xrralrecnnle.mm"
include "mpbird.mm"
include "eliocd.mm"
include "ralrimiva.mm"
include "dfss3.mm"
include "sylibr.mm"
include "xrleidd.mm"
include "crp.mm"
include "1rp.mm"
include "nnrp.mm"
include "rpdivcld.mm"
include "ltaddrpd.mm"
include "iocssioo.mm"
include "syl22anc.mm"
include "ssiin.mm"
include "eqssd.mm"

theorem iooiinioc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vx: setvar x
  assume iooiinioc.1: |- ( ph -> A e. RR* )
  assume iooiinioc.2: |- ( ph -> B e. RR )

  disjoint A n
  disjoint B n
  disjoint n ph
  disjoint A x
  disjoint n x
  disjoint B x
  disjoint ph x
  assert |- ( ph -> |^|_ n e. NN ( A (,) ( B + ( 1 / n ) ) ) = ( A (,] B ) )

  proof
    wph
    vn
    cn
    cA
    cB
    c1
    vn
    cv
    #
    cdiv
    co
    #
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
    cioc
    co
    #
    wph
    vx
    cv
    #
    @5
    wcel
    #
    vx
    @4
    wral
    @4
    @5
    wss
    wph
    @7
    vx
    @4
    wph
    @6
    @4
    wcel
    #
    wa
    #
    cA
    cB
    @6
    wph
    cA
    cxr
    wcel
    #
    @8
    iooiinioc.1
    adantr
    #
    @9
    cB
    wph
    cB
    cr
    wcel
    #
    @8
    iooiinioc.2
    adantr
    #
    rexrd
    @9
    @6
    @9
    @4
    cr
    @6
    @4
    cr
    wss
    #
    @9
    @3
    cr
    wss
    #
    vn
    cn
    wrex
    #
    @14
    c1
    cn
    wcel
    #
    cA
    cB
    c1
    c1
    cdiv
    co
    #
    caddc
    co
    #
    cioo
    co
    #
    cr
    wss
    #
    @16
    1nn
    cA
    @19
    ioossre
    @15
    @21
    vn
    c1
    cn
    @0
    c1
    wceq
    #
    @3
    @20
    cr
    @22
    @2
    @19
    cA
    cioo
    @22
    @1
    @18
    cB
    caddc
    @0
    c1
    c1
    cdiv
    oveq2
    oveq2d
    oveq2d
    #
    sseq1d
    rspcev
    mp2an
    vn
    cn
    @3
    cr
    iinss
    ax-mp
    a1i
    wph
    @8
    simpr
    sseldd
    rexrd
    #
    @9
    @10
    @19
    cxr
    wcel
    #
    @6
    @20
    wcel
    #
    cA
    @6
    clt
    wbr
    @11
    wph
    @25
    @8
    wph
    @19
    wph
    cB
    @18
    iooiinioc.2
    wph
    c1
    c1
    wph
    1red
    #
    @27
    c1
    cc0
    wne
    wph
    ax-1ne0
    a1i
    redivcld
    readdcld
    rexrd
    adantr
    @8
    @26
    wph
    @8
    vn
    @6
    cn
    @3
    @20
    c1
    @8
    id
    @17
    @8
    1nn
    a1i
    @22
    @3
    @20
    @6
    @23
    eleq2d
    eliind
    adantl
    cA
    @19
    @6
    ioogtlb
    syl3anc
    @9
    @6
    cB
    cle
    wbr
    @6
    @2
    cle
    wbr
    #
    vn
    cn
    wral
    @9
    @28
    vn
    cn
    wph
    @8
    vn
    wph
    vn
    nfv
    vn
    @6
    @4
    vn
    @6
    nfcv
    vn
    cn
    @3
    nfii1
    nfel
    nfan
    #
    @9
    @0
    cn
    wcel
    #
    @28
    @9
    @30
    wa
    wph
    @6
    @3
    wcel
    #
    @30
    @28
    wph
    @8
    @30
    simpll
    @8
    @30
    @31
    wph
    @8
    @30
    wa
    @4
    @3
    @6
    @30
    @4
    @3
    wss
    @8
    vn
    cn
    @3
    iinss2
    adantl
    @8
    @30
    simpl
    sseldd
    adantll
    @9
    @30
    simpr
    wph
    @31
    wa
    @30
    wa
    #
    @6
    @2
    @31
    @30
    @6
    cr
    wcel
    #
    wph
    @31
    @33
    @30
    @6
    cA
    @2
    elioore
    adantr
    adantll
    wph
    @30
    @2
    cr
    wcel
    @31
    wph
    @30
    wa
    #
    cB
    @1
    wph
    @12
    @30
    iooiinioc.2
    adantr
    #
    @30
    @1
    cr
    wcel
    wph
    @0
    nnrecre
    adantl
    readdcld
    #
    adantlr
    @32
    @10
    @2
    cxr
    wcel
    #
    @31
    @6
    @2
    clt
    wbr
    wph
    @30
    @10
    @31
    wph
    @10
    @30
    iooiinioc.1
    adantr
    #
    adantlr
    wph
    @30
    @37
    @31
    @34
    @2
    @36
    rexrd
    #
    adantlr
    wph
    @31
    @30
    simplr
    cA
    @2
    @6
    iooltub
    syl3anc
    ltled
    syl21anc
    ex
    ralrimi
    @9
    @6
    cB
    vn
    @29
    @24
    @13
    xrralrecnnle
    mpbird
    eliocd
    ralrimiva
    vx
    @4
    @5
    dfss3
    sylibr
    wph
    @5
    @3
    wss
    #
    vn
    cn
    wral
    @5
    @4
    wss
    wph
    @40
    vn
    cn
    @34
    @10
    @37
    cA
    cA
    cle
    wbr
    #
    cB
    @2
    clt
    wbr
    @40
    @38
    @39
    wph
    @41
    @30
    wph
    cA
    iooiinioc.1
    xrleidd
    adantr
    @34
    cB
    @1
    @35
    @30
    @1
    crp
    wcel
    wph
    @30
    c1
    @0
    c1
    crp
    wcel
    @30
    1rp
    a1i
    @0
    nnrp
    rpdivcld
    adantl
    ltaddrpd
    cA
    @2
    cA
    cB
    iocssioo
    syl22anc
    ralrimiva
    vn
    cn
    @3
    @5
    ssiin
    sylibr
    eqssd
end
