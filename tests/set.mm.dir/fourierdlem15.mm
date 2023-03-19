include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wfn.mm"
include "crn.mm"
include "cicc.mm"
include "wss.mm"
include "wf.mm"
include "cr.mm"
include "cmap.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "cn.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "ovex.mm"
include "elmapd.mm"
include "ffn.mm"
include "simprd.mm"
include "cuz.mm"
include "cn0.mm"
include "nnnn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "adantr.mm"
include "eluzfz2.mm"
include "ffvelrnda.mm"
include "cle.mm"
include "eqcomd.mm"
include "elfzuz.mm"
include "adantl.mm"
include "ad2antrr.mm"
include "elfzle1.mm"
include "elfzelz.mm"
include "zred.mm"
include "elfzel2.mm"
include "elfzle2.mm"
include "letrd.mm"
include "cz.mm"
include "0zd.mm"
include "elfz.mm"
include "syl3anc.mm"
include "mpbir2and.mm"
include "adantll.mm"
include "cmin.mm"
include "simpll.mm"
include "peano2rem.mm"
include "ltm1d.mm"
include "lelttrd.mm"
include "ltletrd.mm"
include "elfzo.mm"
include "elfzofz.mm"
include "fzofzp1.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "r19.21bi.mm"
include "chvarv.mm"
include "ltled.mm"
include "syl2anc.mm"
include "monoord.mm"
include "eqbrtrd.mm"
include "elfzuz3.mm"
include "fz0fzelfz0.mm"
include "0red.mm"
include "nnred.mm"
include "1red.mm"
include "resubcld.mm"
include "adantlr.mm"
include "ad2antlr.mm"
include "0le1.mm"
include "addge0d.mm"
include "leadd1dd.mm"
include "cc.mm"
include "nncnd.mm"
include "1cnd.mm"
include "npcand.mm"
include "breqtrd.mm"
include "peano2zd.mm"
include "eliccd.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem fourierdlem15
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vi: setvar i
  let vm: setvar m
  let cM: class M
  let vp: setvar p
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem15.1: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = A /\ ( p ` m ) = B ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem15.2: |- ( ph -> M e. NN )
  assume fourierdlem15.3: |- ( ph -> Q e. ( P ` M ) )

  disjoint A i
  disjoint A m
  disjoint A p
  disjoint i m
  disjoint i p
  disjoint m p
  disjoint B i
  disjoint B m
  disjoint B p
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint Q i
  disjoint Q p
  disjoint i ph
  disjoint M j
  disjoint i j
  disjoint Q j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> Q : ( 0 ... M ) --> ( A [,] B ) )

  proof
    wph
    cQ
    cc0
    cM
    cfz
    co
    #
    wfn
    #
    cQ
    crn
    cA
    cB
    cicc
    co
    #
    wss
    #
    @0
    @2
    cQ
    wf
    wph
    @0
    cr
    cQ
    wf
    #
    @1
    wph
    cQ
    cr
    @0
    cmap
    co
    wcel
    #
    @4
    wph
    @5
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
    @11
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
    #
    wph
    cQ
    cM
    cP
    cfv
    wcel
    #
    @5
    @18
    wa
    #
    fourierdlem15.3
    wph
    cM
    cn
    wcel
    #
    @19
    @20
    wb
    fourierdlem15.2
    cA
    cB
    cP
    cQ
    vi
    vm
    cM
    vp
    fourierdlem15.1
    fourierdlem2
    syl
    mpbid
    #
    simpld
    wph
    cr
    @0
    cQ
    cvv
    cvv
    cr
    cvv
    wcel
    wph
    reex
    a1i
    @0
    cvv
    wcel
    wph
    cc0
    cM
    cfz
    ovex
    a1i
    elmapd
    mpbid
    #
    @0
    cr
    cQ
    ffn
    syl
    #
    wph
    @1
    @12
    @2
    wcel
    #
    vi
    @0
    wral
    @3
    @24
    wph
    @25
    vi
    @0
    wph
    @11
    @0
    wcel
    #
    wa
    #
    cA
    cB
    @12
    wph
    cA
    cr
    wcel
    @26
    wph
    @6
    cA
    cr
    wph
    @7
    @9
    wph
    @10
    @17
    wph
    @5
    @18
    @22
    simprd
    #
    simpld
    #
    simpld
    #
    wph
    @0
    cr
    cc0
    cQ
    @23
    wph
    cM
    cc0
    cuz
    cfv
    #
    wcel
    #
    cc0
    @0
    wcel
    wph
    @21
    @32
    fourierdlem15.2
    @21
    cM
    cn0
    @31
    cM
    nnnn0
    nn0uz
    syl6eleq
    syl
    #
    cc0
    cM
    eluzfz1
    syl
    ffvelrnd
    eqeltrrd
    adantr
    wph
    cB
    cr
    wcel
    @26
    wph
    @8
    cB
    cr
    wph
    @7
    @9
    @29
    simprd
    #
    wph
    @0
    cr
    cM
    cQ
    @23
    wph
    @32
    cM
    @0
    wcel
    @33
    cc0
    cM
    eluzfz2
    syl
    ffvelrnd
    eqeltrrd
    adantr
    wph
    @0
    cr
    @11
    cQ
    @23
    ffvelrnda
    @27
    cA
    @6
    @12
    cle
    wph
    cA
    @6
    wceq
    @26
    wph
    @6
    cA
    @30
    eqcomd
    adantr
    @27
    vj
    cQ
    cc0
    @11
    @26
    @11
    @31
    wcel
    wph
    @11
    cc0
    cM
    elfzuz
    adantl
    @27
    vj
    cv
    #
    cc0
    @11
    cfz
    co
    wcel
    #
    wa
    @0
    cr
    @35
    cQ
    wph
    @4
    @26
    @36
    @23
    ad2antrr
    @26
    @36
    @35
    @0
    wcel
    #
    wph
    @26
    @36
    wa
    #
    @37
    cc0
    @35
    cle
    wbr
    #
    @35
    cM
    cle
    wbr
    #
    @36
    @39
    @26
    @35
    cc0
    @11
    elfzle1
    adantl
    @38
    @35
    @11
    cM
    @36
    @35
    cr
    wcel
    #
    @26
    @36
    @35
    @35
    cc0
    @11
    elfzelz
    #
    zred
    adantl
    @26
    @11
    cr
    wcel
    #
    @36
    @26
    @11
    @11
    cc0
    cM
    elfzelz
    zred
    #
    adantr
    @26
    cM
    cr
    wcel
    #
    @36
    @26
    cM
    @11
    cc0
    cM
    elfzel2
    #
    zred
    #
    adantr
    @36
    @35
    @11
    cle
    wbr
    @26
    @35
    cc0
    @11
    elfzle2
    adantl
    @26
    @11
    cM
    cle
    wbr
    #
    @36
    @11
    cc0
    cM
    elfzle2
    #
    adantr
    letrd
    @38
    @35
    cz
    wcel
    #
    cc0
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    @37
    @39
    @40
    wa
    wb
    #
    @36
    @50
    @26
    @42
    adantl
    @38
    0zd
    @26
    @52
    @36
    @46
    adantr
    @35
    cc0
    cM
    elfz
    #
    syl3anc
    mpbir2and
    adantll
    ffvelrnd
    @27
    @35
    cc0
    @11
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    wph
    @35
    @16
    wcel
    #
    @35
    cQ
    cfv
    #
    @35
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    cle
    wbr
    wph
    @26
    @56
    simpll
    @26
    @56
    @57
    wph
    @26
    @56
    wa
    #
    @57
    @39
    @35
    cM
    clt
    wbr
    #
    @56
    @39
    @26
    @35
    cc0
    @55
    elfzle1
    adantl
    @61
    @35
    @11
    cM
    @56
    @41
    @26
    @56
    @35
    @35
    cc0
    @55
    elfzelz
    #
    zred
    adantl
    #
    @26
    @43
    @56
    @44
    adantr
    #
    @26
    @45
    @56
    @47
    adantr
    @61
    @35
    @55
    @11
    @64
    @61
    @43
    @55
    cr
    wcel
    @65
    @11
    peano2rem
    syl
    @65
    @56
    @35
    @55
    cle
    wbr
    @26
    @35
    cc0
    @55
    elfzle2
    adantl
    @61
    @11
    @65
    ltm1d
    lelttrd
    @26
    @48
    @56
    @49
    adantr
    ltletrd
    @61
    @50
    @51
    @52
    @57
    @39
    @62
    wa
    wb
    #
    @56
    @50
    @26
    @63
    adantl
    @61
    0zd
    @26
    @52
    @56
    @46
    adantr
    @35
    cc0
    cM
    elfzo
    #
    syl3anc
    mpbir2and
    adantll
    wph
    @57
    wa
    #
    @58
    @60
    @68
    @0
    cr
    @35
    cQ
    wph
    @4
    @57
    @23
    adantr
    #
    @57
    @37
    wph
    @35
    cc0
    cM
    elfzofz
    adantl
    ffvelrnd
    @68
    @0
    cr
    @59
    cQ
    @69
    @57
    @59
    @0
    wcel
    #
    wph
    cc0
    cM
    @35
    fzofzp1
    adantl
    ffvelrnd
    wph
    @11
    @16
    wcel
    #
    wa
    #
    @15
    wi
    @68
    @58
    @60
    clt
    wbr
    #
    wi
    vi
    vj
    @11
    @35
    wceq
    #
    @72
    @68
    @15
    @73
    @74
    @71
    @57
    wph
    @11
    @35
    @16
    eleq1
    anbi2d
    @74
    @12
    @58
    @14
    @60
    clt
    @11
    @35
    cQ
    fveq2
    @74
    @13
    @59
    cQ
    @11
    @35
    c1
    caddc
    oveq1
    fveq2d
    breq12d
    imbi12d
    wph
    @15
    vi
    @16
    wph
    @10
    @17
    @28
    simprd
    r19.21bi
    chvarv
    #
    ltled
    syl2anc
    monoord
    eqbrtrd
    @27
    @12
    @8
    cB
    cle
    @27
    vj
    cQ
    @11
    cM
    @26
    cM
    @11
    cuz
    cfv
    wcel
    wph
    @11
    cc0
    cM
    elfzuz3
    adantl
    @27
    @35
    @11
    cM
    cfz
    co
    wcel
    #
    wa
    @0
    cr
    @35
    cQ
    wph
    @4
    @26
    @76
    @23
    ad2antrr
    @26
    @76
    @37
    wph
    cM
    @35
    @11
    fz0fzelfz0
    adantll
    ffvelrnd
    @27
    @35
    @11
    cM
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    wa
    #
    @58
    @60
    @79
    @0
    cr
    @35
    cQ
    wph
    @4
    @26
    @78
    @23
    ad2antrr
    #
    @79
    @37
    @39
    @40
    @26
    @78
    @39
    wph
    @26
    @78
    wa
    #
    cc0
    @11
    @35
    @81
    0red
    @26
    @43
    @78
    @44
    adantr
    @78
    @41
    @26
    @78
    @35
    @35
    @11
    @77
    elfzelz
    #
    zred
    #
    adantl
    @26
    cc0
    @11
    cle
    wbr
    @78
    @11
    cc0
    cM
    elfzle1
    adantr
    @78
    @11
    @35
    cle
    wbr
    @26
    @35
    @11
    @77
    elfzle1
    adantl
    letrd
    adantll
    #
    wph
    @78
    @40
    @26
    wph
    @78
    wa
    #
    @35
    cM
    @78
    @41
    wph
    @83
    adantl
    #
    wph
    @45
    @78
    wph
    cM
    fourierdlem15.2
    nnred
    adantr
    #
    @85
    @35
    @77
    cM
    @86
    @85
    cM
    c1
    @87
    @85
    1red
    #
    resubcld
    #
    @87
    @78
    @35
    @77
    cle
    wbr
    wph
    @35
    @11
    @77
    elfzle2
    adantl
    #
    @85
    cM
    @87
    ltm1d
    lelttrd
    #
    ltled
    adantlr
    @79
    @50
    @51
    @52
    @53
    @78
    @50
    @27
    @82
    adantl
    #
    @79
    0zd
    #
    @26
    @52
    wph
    @78
    @46
    ad2antlr
    #
    @54
    syl3anc
    mpbir2and
    ffvelrnd
    @79
    @0
    cr
    @59
    cQ
    @80
    @79
    @70
    cc0
    @59
    cle
    wbr
    #
    @59
    cM
    cle
    wbr
    #
    @79
    @35
    c1
    @78
    @41
    @27
    @83
    adantl
    @79
    1red
    @84
    cc0
    c1
    cle
    wbr
    @79
    0le1
    a1i
    addge0d
    wph
    @78
    @96
    @26
    @85
    @59
    @77
    c1
    caddc
    co
    cM
    cle
    @85
    @35
    @77
    c1
    @86
    @89
    @88
    @90
    leadd1dd
    @85
    cM
    c1
    wph
    cM
    cc
    wcel
    @78
    wph
    cM
    fourierdlem15.2
    nncnd
    adantr
    @85
    1cnd
    npcand
    breqtrd
    adantlr
    @79
    @59
    cz
    wcel
    @51
    @52
    @70
    @95
    @96
    wa
    wb
    @79
    @35
    @92
    peano2zd
    @93
    @94
    @59
    cc0
    cM
    elfz
    syl3anc
    mpbir2and
    ffvelrnd
    @79
    wph
    @57
    @73
    wph
    @26
    @78
    simpll
    @79
    @57
    @39
    @62
    @84
    wph
    @78
    @62
    @26
    @91
    adantlr
    @79
    @50
    @51
    @52
    @66
    @92
    @93
    @94
    @67
    syl3anc
    mpbir2and
    @75
    syl2anc
    ltled
    monoord
    wph
    @9
    @26
    @34
    adantr
    breqtrd
    eliccd
    ralrimiva
    vi
    @0
    @2
    cQ
    fnfvrnss
    syl2anc
    @0
    @2
    cQ
    df-f
    sylanbrc
end
