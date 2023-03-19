include "cuhgr.mm"
include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cpr.mm"
include "cv.mm"
include "ccycls.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "c3.mm"
include "wceq.mm"
include "cc0.mm"
include "wex.mm"
include "ciedg.mm"
include "cdm.mm"
include "wrex.mm"
include "wb.mm"
include "cedg.mm"
include "eleq2i.mm"
include "eqid.mm"
include "uhgredgiedgb.mm"
include "syl5bb.mm"
include "3anbi123d.mm"
include "adantr.mm"
include "wi.mm"
include "cs3.mm"
include "cs4.mm"
include "3simpa.mm"
include "pm3.22.mm"
include "3adant2.mm"
include "jca.mm"
include "ad2antlr.mm"
include "necom.mm"
include "biimpi.mm"
include "anim1i.mm"
include "ancomd.mm"
include "3ad2ant2.mm"
include "3jca.mm"
include "adantl.mm"
include "wss.mm"
include "eqimss.mm"
include "3ad2ant3.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "simp1.mm"
include "anim12i.mm"
include "uhgr3cyclexlem.mm"
include "syl2an.mm"
include "3simpc.mm"
include "necomd.mm"
include "exp31.mm"
include "3adant3.mm"
include "com12.mm"
include "impcom.mm"
include "eqidd.mm"
include "3cyclpd.mm"
include "cvv.mm"
include "cword.mm"
include "s3cli.mm"
include "elexi.mm"
include "s4cli.mm"
include "breq12.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "spc2ev.mm"
include "syl.mm"
include "expcom.mm"
include "3exp.mm"
include "rexlimiva.mm"
include "com13.mm"
include "3imp.mm"
include "sylbid.mm"
include "3impia.mm"

theorem uhgr3cyclex
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cE: class E
  let cG: class G
  let cV: class V
  let vp: setvar p
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  assume uhgr3cyclex.v: |- V = ( Vtx ` G )
  assume uhgr3cyclex.e: |- E = ( Edg ` G )

  disjoint A f
  disjoint A p
  disjoint f p
  disjoint B f
  disjoint B p
  disjoint C f
  disjoint C p
  disjoint G f
  disjoint G p
  disjoint A i
  disjoint A j
  disjoint A k
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint i j
  disjoint i k
  disjoint i p
  disjoint j k
  disjoint j p
  disjoint k p
  disjoint B i
  disjoint B j
  disjoint B k
  disjoint C i
  disjoint C j
  disjoint C k
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint V i
  disjoint V j
  disjoint V k
  assert |- ( ( G e. UHGraph /\ ( ( A e. V /\ B e. V /\ C e. V ) /\ ( A =/= B /\ A =/= C /\ B =/= C ) ) /\ ( { A , B } e. E /\ { B , C } e. E /\ { C , A } e. E ) ) -> E. f E. p ( f ( Cycles ` G ) p /\ ( # ` f ) = 3 /\ ( p ` 0 ) = A ) )

  proof
    cG
    cuhgr
    wcel
    #
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    w3a
    #
    wa
    #
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    cB
    cC
    cpr
    #
    cE
    wcel
    #
    cC
    cA
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    vf
    cv
    #
    vp
    cv
    #
    cG
    ccycls
    cfv
    #
    wbr
    #
    @17
    chash
    cfv
    #
    c3
    wceq
    #
    cc0
    @18
    cfv
    #
    cA
    wceq
    #
    w3a
    #
    vp
    wex
    vf
    wex
    #
    @0
    @9
    wa
    #
    @16
    @10
    vi
    cv
    #
    cG
    ciedg
    cfv
    #
    cfv
    #
    wceq
    #
    vi
    @29
    cdm
    #
    wrex
    #
    @12
    vj
    cv
    #
    @29
    cfv
    #
    wceq
    #
    vj
    @32
    wrex
    #
    @14
    vk
    cv
    #
    @29
    cfv
    #
    wceq
    #
    vk
    @32
    wrex
    #
    w3a
    #
    @26
    @0
    @16
    @42
    wb
    @9
    @0
    @11
    @33
    @13
    @37
    @15
    @41
    @11
    @10
    cG
    cedg
    cfv
    #
    wcel
    @0
    @33
    cE
    @43
    @10
    uhgr3cyclex.e
    eleq2i
    vi
    @10
    cG
    @29
    @29
    eqid
    #
    uhgredgiedgb
    syl5bb
    @13
    @12
    @43
    wcel
    @0
    @37
    cE
    @43
    @12
    uhgr3cyclex.e
    eleq2i
    vj
    @12
    cG
    @29
    @44
    uhgredgiedgb
    syl5bb
    @15
    @14
    @43
    wcel
    @0
    @41
    cE
    @43
    @14
    uhgr3cyclex.e
    eleq2i
    vk
    @14
    cG
    @29
    @44
    uhgredgiedgb
    syl5bb
    3anbi123d
    adantr
    @42
    @27
    @26
    @33
    @37
    @41
    @27
    @26
    wi
    #
    @31
    @37
    @41
    @45
    wi
    wi
    vi
    @32
    @41
    @37
    @28
    @32
    wcel
    #
    @31
    wa
    #
    @45
    @40
    @37
    @47
    @45
    wi
    #
    wi
    vk
    @32
    @37
    @38
    @32
    wcel
    #
    @40
    wa
    #
    @48
    @36
    @50
    @48
    wi
    vj
    @32
    @34
    @32
    wcel
    #
    @36
    wa
    #
    @50
    @47
    @45
    @27
    @52
    @50
    @47
    w3a
    #
    @26
    @27
    @53
    wa
    #
    @28
    @34
    @38
    cs3
    #
    cA
    cB
    cC
    cA
    cs4
    #
    @19
    wbr
    #
    @55
    chash
    cfv
    #
    c3
    wceq
    #
    cc0
    @56
    cfv
    #
    cA
    wceq
    #
    w3a
    #
    @26
    @54
    cA
    cB
    cC
    cA
    @56
    @55
    cG
    @29
    @28
    @34
    @38
    cV
    @56
    eqid
    @55
    eqid
    @9
    @1
    @2
    wa
    #
    @3
    @1
    wa
    #
    wa
    #
    @0
    @53
    @4
    @65
    @8
    @4
    @63
    @64
    @1
    @2
    @3
    3simpa
    @1
    @3
    @64
    @2
    @1
    @3
    pm3.22
    3adant2
    jca
    adantr
    ad2antlr
    @9
    @5
    @6
    wa
    #
    @7
    cB
    cA
    wne
    #
    wa
    #
    cC
    cA
    wne
    #
    w3a
    #
    @0
    @53
    @8
    @70
    @4
    @8
    @66
    @68
    @69
    @5
    @6
    @7
    3simpa
    @5
    @7
    @68
    @6
    @5
    @7
    wa
    @67
    @7
    @5
    @67
    @7
    @5
    @67
    cA
    cB
    necom
    biimpi
    anim1i
    ancomd
    3adant2
    @6
    @5
    @69
    @7
    @6
    @69
    cA
    cC
    necom
    biimpi
    3ad2ant2
    #
    3jca
    adantl
    ad2antlr
    @53
    @10
    @30
    wss
    #
    @12
    @35
    wss
    #
    @14
    @39
    wss
    #
    w3a
    @27
    @53
    @72
    @73
    @74
    @47
    @52
    @72
    @50
    @31
    @72
    @46
    @10
    @30
    eqimss
    adantl
    3ad2ant3
    @52
    @50
    @73
    @47
    @36
    @73
    @51
    @12
    @35
    eqimss
    adantl
    3ad2ant1
    @50
    @52
    @74
    @47
    @40
    @74
    @49
    @14
    @39
    eqimss
    adantl
    3ad2ant2
    3jca
    adantl
    uhgr3cyclex.v
    @44
    @54
    @28
    @34
    wne
    #
    @28
    @38
    wne
    #
    @34
    @38
    wne
    #
    @27
    @64
    @69
    wa
    #
    @47
    @52
    wa
    #
    @75
    @53
    @9
    @78
    @0
    @4
    @64
    @8
    @69
    @4
    @3
    @1
    @1
    @2
    @3
    simp3
    @1
    @2
    @3
    simp1
    jca
    @71
    anim12i
    adantl
    @52
    @47
    @79
    @50
    @52
    @47
    pm3.22
    3adant2
    cC
    cA
    cB
    cE
    cG
    @29
    @28
    @34
    cV
    uhgr3cyclex.v
    uhgr3cyclex.e
    @44
    uhgr3cyclexlem
    syl2an
    @27
    @2
    @3
    wa
    #
    @7
    wa
    #
    @50
    @47
    wa
    #
    @76
    @53
    @9
    @81
    @0
    @4
    @80
    @8
    @7
    @1
    @2
    @3
    3simpc
    @5
    @6
    @7
    simp3
    anim12i
    adantl
    @52
    @50
    @47
    3simpc
    @81
    @82
    wa
    @38
    @28
    cB
    cC
    cA
    cE
    cG
    @29
    @38
    @28
    cV
    uhgr3cyclex.v
    uhgr3cyclex.e
    @44
    uhgr3cyclexlem
    necomd
    syl2an
    @53
    @27
    @77
    @52
    @50
    @27
    @77
    wi
    @47
    @27
    @52
    @50
    wa
    #
    @77
    @9
    @83
    @77
    wi
    #
    @0
    @8
    @4
    @84
    @5
    @6
    @4
    @84
    wi
    @7
    @4
    @5
    @84
    @1
    @2
    @5
    @84
    wi
    @3
    @63
    @5
    @83
    @77
    cA
    cB
    cC
    cE
    cG
    @29
    @34
    @38
    cV
    uhgr3cyclex.v
    uhgr3cyclex.e
    @44
    uhgr3cyclexlem
    exp31
    3adant3
    com12
    3ad2ant1
    impcom
    adantl
    com12
    3adant3
    impcom
    3jca
    @54
    cA
    eqidd
    3cyclpd
    @25
    @62
    vf
    vp
    @55
    @56
    @55
    cvv
    cword
    #
    @28
    @34
    @38
    s3cli
    elexi
    @56
    @85
    cA
    cB
    cC
    cA
    s4cli
    elexi
    @17
    @55
    wceq
    #
    @18
    @56
    wceq
    #
    wa
    @20
    @57
    @22
    @59
    @24
    @61
    @17
    @55
    @18
    @56
    @19
    breq12
    @86
    @22
    @59
    wb
    @87
    @86
    @21
    @58
    c3
    @17
    @55
    chash
    fveq2
    eqeq1d
    adantr
    @87
    @24
    @61
    wb
    @86
    @87
    @23
    @60
    cA
    cc0
    @18
    @56
    fveq1
    eqeq1d
    adantl
    3anbi123d
    spc2ev
    syl
    expcom
    3exp
    rexlimiva
    com12
    rexlimiva
    com13
    rexlimiva
    3imp
    com12
    sylbid
    3impia
end
