include "cuni.mm"
include "cdif.mm"
include "ccrd.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wpss.mm"
include "wn.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "csuc.mm"
include "fvex.mm"
include "sucid.mm"
include "ttukeylem6.mm"
include "mpan2.mm"
include "c0.mm"
include "ttukeylem4.mm"
include "con0.mm"
include "w3a.mm"
include "0elon.mm"
include "cardon.mm"
include "0ss.mm"
include "3pm3.2i.mm"
include "ttukeylem5.mm"
include "eqsstr3d.mm"
include "wceq.mm"
include "wi.mm"
include "simprr.mm"
include "cun.mm"
include "ssun1.mm"
include "undif1.mm"
include "sseqtr4i.mm"
include "ccnv.mm"
include "simpl.mm"
include "wf.mm"
include "wf1o.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "adantr.mm"
include "eldifi.mm"
include "ad2antll.mm"
include "simprll.mm"
include "elunii.mm"
include "syl2anc.mm"
include "eldifn.mm"
include "eldifd.mm"
include "ffvelrnd.mm"
include "onelon.mm"
include "sylancr.mm"
include "suceloni.mm"
include "syl.mm"
include "a1i.mm"
include "word.mm"
include "onordi.mm"
include "ordsucss.mm"
include "mpsyl.mm"
include "syl13anc.mm"
include "csn.mm"
include "cif.mm"
include "ssun2.mm"
include "eloni.mm"
include "ordunisuc.mm"
include "fveq2d.mm"
include "f1ocnvfv2.mm"
include "eqtr2d.mm"
include "velsn.mm"
include "sylibr.mm"
include "ordelss.mm"
include "eqsstrd.mm"
include "simprlr.mm"
include "sstrd.mm"
include "eqeltrrd.mm"
include "snssd.mm"
include "unssd.mm"
include "ttukeylem2.mm"
include "syl12anc.mm"
include "iftrued.mm"
include "eleqtrrd.mm"
include "sseldi.mm"
include "cima.mm"
include "ttukeylem3.mm"
include "syldan.mm"
include "wne.mm"
include "sucidg.mm"
include "ordirr.mm"
include "nelne1.mm"
include "neeqtrrd.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "sseldd.mm"
include "expr.mm"
include "ssrdv.mm"
include "syl5ss.mm"
include "eqssd.mm"
include "npss.mm"
include "ralrimiva.mm"
include "sseq2.mm"
include "psseq1.mm"
include "notbid.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rspcev.mm"

theorem ttukeylem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let va: setvar a
  let cC: class C
  let cD: class D
  let vf: setvar f
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume ttukeylem.1: |- ( ph -> F : ( card ` ( U. A \ B ) ) -1-1-onto-> ( U. A \ B ) )
  assume ttukeylem.2: |- ( ph -> B e. A )
  assume ttukeylem.3: |- ( ph -> A. x ( x e. A <-> ( ~P x i^i Fin ) C_ A ) )
  assume ttukeylem.4: |- G = recs ( ( z e. _V |-> if ( dom z = U. dom z , if ( dom z = (/) , B , U. ran z ) , ( ( z ` U. dom z ) u. if ( ( ( z ` U. dom z ) u. { ( F ` U. dom z ) } ) e. A , { ( F ` U. dom z ) } , (/) ) ) ) ) )

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph y
  disjoint ph z
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint F x
  disjoint F z
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint C a
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D x
  disjoint D y
  disjoint a f
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint G a
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint G f
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint G v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint G w
  disjoint a ph
  disjoint f ph
  disjoint ph u
  disjoint ph w
  disjoint A a
  disjoint A f
  disjoint A u
  disjoint A w
  disjoint B a
  disjoint B f
  disjoint B u
  disjoint B w
  assert |- ( ph -> E. x e. A ( B C_ x /\ A. y e. A -. x C. y ) )

  proof
    wph
    cA
    cuni
    #
    cB
    cdif
    #
    ccrd
    cfv
    #
    cG
    cfv
    #
    cA
    wcel
    #
    cB
    @3
    wss
    #
    @3
    vy
    cv
    #
    wpss
    #
    wn
    #
    vy
    cA
    wral
    #
    cB
    vx
    cv
    #
    wss
    #
    @10
    @6
    wpss
    #
    wn
    #
    vy
    cA
    wral
    #
    wa
    #
    vx
    cA
    wrex
    wph
    @2
    @2
    csuc
    wcel
    @4
    @2
    @1
    ccrd
    fvex
    sucid
    wph
    vx
    vz
    cA
    cB
    @2
    cF
    cG
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem.4
    ttukeylem6
    mpan2
    wph
    cB
    c0
    cG
    cfv
    #
    @3
    wph
    vx
    vz
    cA
    cB
    cF
    cG
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem.4
    ttukeylem4
    wph
    c0
    con0
    wcel
    #
    @2
    con0
    wcel
    #
    c0
    @2
    wss
    #
    w3a
    @16
    @3
    wss
    @17
    @18
    @19
    0elon
    @1
    cardon
    #
    @2
    0ss
    3pm3.2i
    wph
    vx
    vz
    cA
    cB
    c0
    @2
    cF
    cG
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem.4
    ttukeylem5
    mpan2
    eqsstr3d
    #
    wph
    @8
    vy
    cA
    wph
    @6
    cA
    wcel
    #
    wa
    @3
    @6
    wss
    #
    @3
    @6
    wceq
    #
    wi
    @8
    wph
    @22
    @23
    @24
    wph
    @22
    @23
    wa
    #
    wa
    #
    @3
    @6
    wph
    @22
    @23
    simprr
    @26
    @6
    @6
    cB
    cdif
    #
    cB
    cun
    #
    @3
    @6
    @6
    cB
    cun
    @28
    @6
    cB
    ssun1
    @6
    cB
    undif1
    sseqtr4i
    @26
    @27
    cB
    @3
    @26
    va
    @27
    @3
    wph
    @25
    va
    cv
    #
    @27
    wcel
    #
    @29
    @3
    wcel
    wph
    @25
    @30
    wa
    #
    wa
    #
    @29
    cF
    ccnv
    #
    cfv
    #
    csuc
    #
    cG
    cfv
    #
    @3
    @29
    @32
    wph
    @35
    con0
    wcel
    #
    @18
    @35
    @2
    wss
    #
    @36
    @3
    wss
    wph
    @31
    simpl
    #
    @32
    @34
    con0
    wcel
    #
    @37
    @32
    @18
    @34
    @2
    wcel
    #
    @40
    @20
    @32
    @1
    @2
    @29
    @33
    wph
    @1
    @2
    @33
    wf
    #
    @31
    wph
    @2
    @1
    cF
    wf1o
    #
    @1
    @2
    @33
    wf1o
    @42
    ttukeylem.1
    @2
    @1
    cF
    f1ocnv
    @1
    @2
    @33
    f1of
    3syl
    adantr
    @32
    @29
    @0
    cB
    @32
    @29
    @6
    wcel
    #
    @22
    @29
    @0
    wcel
    @30
    @44
    wph
    @25
    @29
    @6
    cB
    eldifi
    ad2antll
    #
    wph
    @22
    @23
    @30
    simprll
    #
    @29
    @6
    cA
    elunii
    syl2anc
    @30
    @29
    cB
    wcel
    wn
    wph
    @25
    @29
    @6
    cB
    eldifn
    ad2antll
    eldifd
    #
    ffvelrnd
    #
    @2
    @34
    onelon
    sylancr
    #
    @34
    suceloni
    syl
    #
    @18
    @32
    @20
    a1i
    #
    @2
    word
    #
    @32
    @41
    @38
    @2
    @20
    onordi
    #
    @48
    @34
    @2
    ordsucss
    mpsyl
    wph
    vx
    vz
    cA
    cB
    @35
    @2
    cF
    cG
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem.4
    ttukeylem5
    syl13anc
    @32
    @29
    @35
    cuni
    #
    cG
    cfv
    #
    @55
    @54
    cF
    cfv
    #
    csn
    #
    cun
    #
    cA
    wcel
    #
    @57
    c0
    cif
    #
    cun
    #
    @36
    @32
    @60
    @61
    @29
    @60
    @55
    ssun2
    @32
    @29
    @57
    @60
    @32
    @29
    @56
    wceq
    @29
    @57
    wcel
    @32
    @56
    @34
    cF
    cfv
    #
    @29
    @32
    @54
    @34
    cF
    @32
    @40
    @34
    word
    #
    @54
    @34
    wceq
    @49
    @34
    eloni
    #
    @34
    ordunisuc
    3syl
    #
    fveq2d
    @32
    @43
    @29
    @1
    wcel
    @62
    @29
    wceq
    wph
    @43
    @31
    ttukeylem.1
    adantr
    @47
    @2
    @1
    @29
    cF
    f1ocnvfv2
    syl2anc
    eqtr2d
    #
    va
    @56
    velsn
    sylibr
    @32
    @59
    @57
    c0
    @32
    wph
    @22
    @58
    @6
    wss
    @59
    @39
    @46
    @32
    @55
    @57
    @6
    @32
    @55
    @3
    @6
    @32
    @55
    @34
    cG
    cfv
    #
    @3
    @32
    @54
    @34
    cG
    @65
    fveq2d
    @32
    wph
    @40
    @18
    @34
    @2
    wss
    #
    @67
    @3
    wss
    @39
    @49
    @51
    @32
    @52
    @41
    @68
    @53
    @48
    @2
    @34
    ordelss
    sylancr
    wph
    vx
    vz
    cA
    cB
    @34
    @2
    cF
    cG
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem.4
    ttukeylem5
    syl13anc
    eqsstrd
    wph
    @22
    @23
    @30
    simprlr
    sstrd
    @32
    @56
    @6
    @32
    @29
    @56
    @6
    @66
    @45
    eqeltrrd
    snssd
    unssd
    wph
    vx
    cA
    cB
    @6
    @58
    cF
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem2
    syl12anc
    iftrued
    eleqtrrd
    sseldi
    @32
    @36
    @35
    @54
    wceq
    #
    @35
    c0
    wceq
    cB
    cG
    @35
    cima
    cuni
    cif
    #
    @61
    cif
    #
    @61
    wph
    @31
    @37
    @36
    @71
    wceq
    @50
    wph
    vx
    vz
    cA
    cB
    @35
    cF
    cG
    ttukeylem.1
    ttukeylem.2
    ttukeylem.3
    ttukeylem.4
    ttukeylem3
    syldan
    @32
    @69
    @70
    @61
    @32
    @35
    @54
    @32
    @35
    @34
    @54
    @32
    @34
    @35
    wcel
    #
    @34
    @34
    wcel
    wn
    #
    @35
    @34
    wne
    @32
    @41
    @72
    @48
    @34
    @2
    sucidg
    syl
    @32
    @40
    @63
    @73
    @49
    @64
    @34
    ordirr
    3syl
    @34
    @35
    @34
    nelne1
    syl2anc
    @65
    neeqtrrd
    neneqd
    iffalsed
    eqtrd
    eleqtrrd
    sseldd
    expr
    ssrdv
    wph
    @5
    @25
    @21
    adantr
    unssd
    syl5ss
    eqssd
    expr
    @3
    @6
    npss
    sylibr
    ralrimiva
    @15
    @5
    @9
    wa
    vx
    @3
    cA
    @10
    @3
    wceq
    #
    @11
    @5
    @14
    @9
    @10
    @3
    cB
    sseq2
    @74
    @13
    @8
    vy
    cA
    @74
    @12
    @7
    @10
    @3
    @6
    psseq1
    notbid
    ralbidv
    anbi12d
    rspcev
    syl12anc
end
