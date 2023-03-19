include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cmap.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "wf.mm"
include "cmin.mm"
include "cn.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "elmapi.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "resubcld.mm"
include "fmptd.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "ovex.mm"
include "elmapd.mm"
include "mpbird.mm"
include "cmpt.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "adantl.mm"
include "cz.mm"
include "w3a.mm"
include "cle.mm"
include "0zd.mm"
include "nnzd.mm"
include "3jca.mm"
include "0le0.mm"
include "0red.mm"
include "nnred.mm"
include "nngt0d.mm"
include "ltled.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "ffvelrnd.mm"
include "fvmptd.mm"
include "simprd.mm"
include "recnd.mm"
include "pncand.mm"
include "3eqtrd.mm"
include "leidd.mm"
include "jca.mm"
include "elfzofz.mm"
include "sylan2.mm"
include "fzofzp1.mm"
include "r19.21bi.mm"
include "ltsub1dd.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "3brtr4d.mm"
include "ralrimiva.mm"

theorem fourierdlem14
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vi: setvar i
  let vm: setvar m
  let cM: class M
  let cO: class O
  let cV: class V
  let cX: class X
  let vp: setvar p
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem14.1: |- ( ph -> A e. RR )
  assume fourierdlem14.2: |- ( ph -> B e. RR )
  assume fourierdlem14.x: |- ( ph -> X e. RR )
  assume fourierdlem14.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = ( A + X ) /\ ( p ` m ) = ( B + X ) ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem14.o: |- O = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem14.m: |- ( ph -> M e. NN )
  assume fourierdlem14.v: |- ( ph -> V e. ( P ` M ) )
  assume fourierdlem14.q: |- Q = ( i e. ( 0 ... M ) |-> ( ( V ` i ) - X ) )

  disjoint A m
  disjoint A p
  disjoint m p
  disjoint B m
  disjoint B p
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint i m
  disjoint i p
  disjoint Q i
  disjoint Q p
  disjoint V i
  disjoint V p
  disjoint X i
  disjoint X m
  disjoint X p
  disjoint i ph
  disjoint M j
  disjoint i j
  disjoint V j
  disjoint X j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> Q e. ( O ` M ) )

  proof
    wph
    cQ
    cM
    cO
    cfv
    wcel
    #
    cQ
    cr
    cc0
    cM
    cfz
    co
    #
    cmap
    co
    #
    wcel
    #
    cc0
    cQ
    cfv
    #
    cA
    wceq
    #
    cM
    cQ
    cfv
    #
    cB
    wceq
    #
    wa
    #
    vi
    cv
    #
    cQ
    cfv
    #
    @9
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    clt
    wbr
    #
    vi
    cc0
    cM
    cfzo
    co
    #
    wral
    #
    wa
    wa
    #
    wph
    @3
    @8
    @15
    wph
    @3
    @1
    cr
    cQ
    wf
    wph
    vi
    @1
    @9
    cV
    cfv
    #
    cX
    cmin
    co
    #
    cr
    cQ
    wph
    @9
    @1
    wcel
    #
    wa
    @17
    cX
    wph
    @1
    cr
    @9
    cV
    wph
    cV
    @2
    wcel
    #
    @1
    cr
    cV
    wf
    #
    wph
    @20
    cc0
    cV
    cfv
    #
    cA
    cX
    caddc
    co
    #
    wceq
    #
    cM
    cV
    cfv
    #
    cB
    cX
    caddc
    co
    #
    wceq
    #
    wa
    #
    @17
    @11
    cV
    cfv
    #
    clt
    wbr
    #
    vi
    @14
    wral
    #
    wa
    #
    wph
    cV
    cM
    cP
    cfv
    wcel
    #
    @20
    @32
    wa
    #
    fourierdlem14.v
    wph
    cM
    cn
    wcel
    #
    @33
    @34
    wb
    fourierdlem14.m
    @23
    @26
    cP
    cV
    vi
    vm
    cM
    vp
    fourierdlem14.p
    fourierdlem2
    syl
    mpbid
    #
    simpld
    cV
    cr
    @1
    elmapi
    syl
    #
    ffvelrnda
    #
    wph
    cX
    cr
    wcel
    #
    @19
    fourierdlem14.x
    adantr
    resubcld
    #
    fourierdlem14.q
    fmptd
    wph
    cr
    @1
    cQ
    cvv
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    @1
    cvv
    wcel
    wph
    cc0
    cM
    cfz
    ovex
    a1i
    elmapd
    mpbird
    wph
    @5
    @7
    wph
    @4
    @22
    cX
    cmin
    co
    #
    @23
    cX
    cmin
    co
    cA
    wph
    vi
    cc0
    @18
    @41
    @1
    cQ
    cr
    cQ
    vi
    @1
    @18
    cmpt
    #
    wceq
    wph
    fourierdlem14.q
    a1i
    #
    @9
    cc0
    wceq
    #
    @18
    @41
    wceq
    wph
    @44
    @17
    @22
    cX
    cmin
    @9
    cc0
    cV
    fveq2
    oveq1d
    adantl
    wph
    cc0
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @45
    w3a
    #
    cc0
    cc0
    cle
    wbr
    #
    cc0
    cM
    cle
    wbr
    #
    wa
    wa
    cc0
    @1
    wcel
    wph
    @47
    @48
    @49
    wph
    @45
    @46
    @45
    wph
    0zd
    #
    wph
    cM
    fourierdlem14.m
    nnzd
    #
    @50
    3jca
    @48
    wph
    0le0
    a1i
    wph
    cc0
    cM
    wph
    0red
    wph
    cM
    fourierdlem14.m
    nnred
    #
    wph
    cM
    fourierdlem14.m
    nngt0d
    ltled
    #
    jca32
    cc0
    cc0
    cM
    elfz2
    sylibr
    #
    wph
    @22
    cX
    wph
    @1
    cr
    cc0
    cV
    @37
    @54
    ffvelrnd
    fourierdlem14.x
    resubcld
    fvmptd
    wph
    @22
    @23
    cX
    cmin
    wph
    @24
    @27
    wph
    @28
    @31
    wph
    @20
    @32
    @36
    simprd
    #
    simpld
    #
    simpld
    oveq1d
    wph
    cA
    cX
    wph
    cA
    fourierdlem14.1
    recnd
    wph
    cX
    fourierdlem14.x
    recnd
    #
    pncand
    3eqtrd
    wph
    @6
    @25
    cX
    cmin
    co
    #
    @26
    cX
    cmin
    co
    cB
    wph
    vi
    cM
    @18
    @58
    @1
    cQ
    cr
    @43
    @9
    cM
    wceq
    #
    @18
    @58
    wceq
    wph
    @59
    @17
    @25
    cX
    cmin
    @9
    cM
    cV
    fveq2
    oveq1d
    adantl
    wph
    @45
    @46
    @46
    w3a
    #
    @49
    cM
    cM
    cle
    wbr
    #
    wa
    wa
    cM
    @1
    wcel
    wph
    @60
    @49
    @61
    wph
    @45
    @46
    @46
    @50
    @51
    @51
    3jca
    @53
    wph
    cM
    @52
    leidd
    jca32
    cM
    cc0
    cM
    elfz2
    sylibr
    #
    wph
    @25
    cX
    wph
    @1
    cr
    cM
    cV
    @37
    @62
    ffvelrnd
    fourierdlem14.x
    resubcld
    fvmptd
    wph
    @25
    @26
    cX
    cmin
    wph
    @24
    @27
    @56
    simprd
    oveq1d
    wph
    cB
    cX
    wph
    cB
    fourierdlem14.2
    recnd
    @57
    pncand
    3eqtrd
    jca
    wph
    @13
    vi
    @14
    wph
    @9
    @14
    wcel
    #
    wa
    #
    @18
    @29
    cX
    cmin
    co
    #
    @10
    @12
    clt
    @64
    @17
    @29
    cX
    @63
    wph
    @19
    @17
    cr
    wcel
    @9
    cc0
    cM
    elfzofz
    #
    @38
    sylan2
    @64
    @1
    cr
    @11
    cV
    wph
    @21
    @63
    @37
    adantr
    @63
    @11
    @1
    wcel
    wph
    cc0
    cM
    @9
    fzofzp1
    adantl
    #
    ffvelrnd
    #
    wph
    @39
    @63
    fourierdlem14.x
    adantr
    #
    wph
    @30
    vi
    @14
    wph
    @28
    @31
    @55
    simprd
    r19.21bi
    ltsub1dd
    @64
    @19
    @18
    cr
    wcel
    #
    @10
    @18
    wceq
    @63
    @19
    wph
    @66
    adantl
    @63
    wph
    @19
    @70
    @66
    @40
    sylan2
    vi
    @1
    @18
    cr
    cQ
    fourierdlem14.q
    fvmpt2
    syl2anc
    @64
    vj
    @11
    vj
    cv
    #
    cV
    cfv
    #
    cX
    cmin
    co
    #
    @65
    @1
    cQ
    cr
    cQ
    vj
    @1
    @73
    cmpt
    #
    wceq
    @64
    cQ
    @42
    @74
    fourierdlem14.q
    vi
    vj
    @1
    @18
    @73
    @9
    @71
    wceq
    @17
    @72
    cX
    cmin
    @9
    @71
    cV
    fveq2
    oveq1d
    cbvmptv
    eqtri
    a1i
    @71
    @11
    wceq
    #
    @73
    @65
    wceq
    @64
    @75
    @72
    @29
    cX
    cmin
    @71
    @11
    cV
    fveq2
    oveq1d
    adantl
    @67
    @64
    @29
    cX
    @68
    @69
    resubcld
    fvmptd
    3brtr4d
    ralrimiva
    jca32
    wph
    @35
    @0
    @16
    wb
    fourierdlem14.m
    cA
    cB
    cO
    cQ
    vi
    vm
    cM
    vp
    fourierdlem14.o
    fourierdlem2
    syl
    mpbird
end
