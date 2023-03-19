include "con0.mm"
include "c2o.mm"
include "cdif.mm"
include "wcel.mm"
include "c1o.mm"
include "wa.mm"
include "coe.mm"
include "co.mm"
include "wss.mm"
include "csuc.mm"
include "cv.mm"
include "crab.mm"
include "cint.mm"
include "cuni.mm"
include "wrex.mm"
include "eldifi.mm"
include "adantl.mm"
include "suceloni.mm"
include "syl.mm"
include "oeworde.mm"
include "syldan.mm"
include "sucidg.mm"
include "sseldd.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "onintrab2.mm"
include "sylib.mm"
include "onuni.mm"
include "syl5eqel.mm"
include "wn.mm"
include "c0.mm"
include "wlim.mm"
include "wo.mm"
include "wne.mm"
include "dif1o.mm"
include "simprbi.mm"
include "ssrab2.mm"
include "rabn0.mm"
include "sylibr.mm"
include "onint.mm"
include "sylancr.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "elrab.mm"
include "adantr.mm"
include "oe0.mm"
include "el1o.mm"
include "syl6bb.mm"
include "syl5ib.mm"
include "syld.mm"
include "necon3ad.mm"
include "mpd.mm"
include "ciun.mm"
include "limuni.mm"
include "syl6eqr.mm"
include "eqeltrrd.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "ad2antrr.mm"
include "wb.mm"
include "limeq.mm"
include "ibi.mm"
include "anim12i.mm"
include "dif20el.mm"
include "oelim.mm"
include "syl21anc.mm"
include "eleqtrd.mm"
include "eliun.mm"
include "onss.mm"
include "sselda.mm"
include "biimpar.mm"
include "onnminsb.mm"
include "sylc.mm"
include "nrexdv.mm"
include "pm2.65da.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "word.mm"
include "eloni.mm"
include "unizlim.mm"
include "3syl.mm"
include "mtbird.mm"
include "orduniorsuc.mm"
include "ord.mm"
include "suceq.mm"
include "ax-mp.mm"
include "syl6reqr.mm"
include "inteqi.mm"
include "syl6eleq.mm"
include "oecl.mm"
include "ontri1.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "3jca.mm"

theorem oeeulem
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cX: class X
  let va: setvar a
  let vd: setvar d
  let ve: setvar e
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cE: class E
  assume oeeu.1: |- X = U. |^| { x e. On | B e. ( A ^o x ) }

  disjoint A x
  disjoint B x
  disjoint a d
  disjoint a e
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint d e
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint A d
  disjoint e w
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint A e
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B a
  disjoint B d
  disjoint B e
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint D a
  disjoint D d
  disjoint D e
  disjoint E a
  disjoint E d
  disjoint E e
  disjoint X a
  disjoint X d
  disjoint X e
  disjoint X w
  disjoint X y
  disjoint X z
  assert |- ( ( A e. ( On \ 2o ) /\ B e. ( On \ 1o ) ) -> ( X e. On /\ ( A ^o X ) C_ B /\ B e. ( A ^o suc X ) ) )

  proof
    cA
    con0
    c2o
    cdif
    wcel
    #
    cB
    con0
    c1o
    cdif
    wcel
    #
    wa
    #
    cX
    con0
    wcel
    #
    cA
    cX
    coe
    co
    #
    cB
    wss
    #
    cB
    cA
    cX
    csuc
    #
    coe
    co
    #
    wcel
    #
    @2
    cX
    cB
    cA
    vx
    cv
    #
    coe
    co
    #
    wcel
    #
    vx
    con0
    crab
    #
    cint
    #
    cuni
    #
    con0
    oeeu.1
    @2
    @13
    con0
    wcel
    #
    @14
    con0
    wcel
    @2
    @11
    vx
    con0
    wrex
    #
    @15
    @2
    cB
    csuc
    #
    con0
    wcel
    #
    cB
    cA
    @17
    coe
    co
    #
    wcel
    #
    @16
    @2
    cB
    con0
    wcel
    #
    @18
    @1
    @21
    @0
    cB
    con0
    c1o
    eldifi
    adantl
    #
    cB
    suceloni
    syl
    #
    @2
    @17
    @19
    cB
    @0
    @1
    @18
    @17
    @19
    wss
    @23
    cA
    @17
    oeworde
    syldan
    @2
    @21
    cB
    @17
    wcel
    @22
    cB
    con0
    sucidg
    syl
    sseldd
    @11
    @20
    vx
    @17
    con0
    @9
    @17
    wceq
    @10
    @19
    cB
    @9
    @17
    cA
    coe
    oveq2
    eleq2d
    rspcev
    syl2anc
    #
    @11
    vx
    onintrab2
    sylib
    #
    @13
    onuni
    syl
    syl5eqel
    #
    @2
    @5
    cB
    @4
    wcel
    #
    wn
    #
    @2
    @3
    cX
    cB
    cA
    vy
    cv
    #
    coe
    co
    #
    wcel
    #
    vy
    con0
    crab
    #
    cint
    #
    wcel
    @28
    @26
    @2
    cX
    @13
    @33
    @2
    cX
    @6
    @13
    @2
    @3
    cX
    @6
    wcel
    @26
    cX
    con0
    sucidg
    syl
    @2
    @13
    @14
    csuc
    #
    @6
    @2
    @13
    @14
    wceq
    #
    wn
    @13
    @34
    wceq
    #
    @2
    @35
    @13
    c0
    wceq
    #
    @13
    wlim
    #
    wo
    #
    @2
    @37
    wn
    #
    @38
    wn
    @39
    wn
    @2
    cB
    c0
    wne
    #
    @40
    @1
    @41
    @0
    @1
    @21
    @41
    cB
    con0
    dif1o
    simprbi
    adantl
    @2
    @37
    cB
    c0
    @2
    @37
    c0
    @12
    wcel
    #
    cB
    c0
    wceq
    #
    @2
    @13
    @12
    wcel
    #
    @37
    @42
    @2
    @12
    con0
    wss
    @12
    c0
    wne
    #
    @44
    @11
    vx
    con0
    ssrab2
    @2
    @16
    @45
    @24
    @11
    vx
    con0
    rabn0
    sylibr
    @12
    onint
    sylancr
    #
    @13
    c0
    @12
    eleq1
    syl5ibcom
    @42
    cB
    cA
    c0
    coe
    co
    #
    wcel
    #
    @2
    @43
    @42
    c0
    con0
    wcel
    @48
    @11
    @48
    vx
    c0
    con0
    @9
    c0
    wceq
    @10
    @47
    cB
    @9
    c0
    cA
    coe
    oveq2
    eleq2d
    elrab
    simprbi
    @2
    @48
    cB
    c1o
    wcel
    @43
    @2
    @47
    c1o
    cB
    @2
    cA
    con0
    wcel
    #
    @47
    c1o
    wceq
    @0
    @49
    @1
    cA
    con0
    c2o
    eldifi
    #
    adantr
    #
    cA
    oe0
    syl
    eleq2d
    cB
    el1o
    syl6bb
    syl5ib
    syld
    necon3ad
    mpd
    @2
    @38
    @31
    vy
    cX
    wrex
    #
    @2
    @38
    wa
    #
    cB
    vy
    cX
    @30
    ciun
    #
    wcel
    @52
    @53
    cB
    @4
    @54
    @53
    cX
    @12
    wcel
    #
    @27
    @53
    @13
    cX
    @12
    @38
    @13
    cX
    wceq
    #
    @2
    @38
    @13
    @14
    cX
    @13
    limuni
    oeeu.1
    syl6eqr
    #
    adantl
    #
    @2
    @44
    @38
    @46
    adantr
    eqeltrrd
    @55
    @3
    @27
    @31
    @27
    vy
    cX
    con0
    @12
    @29
    cX
    wceq
    @30
    @4
    cB
    @29
    cX
    cA
    coe
    oveq2
    eleq2d
    #
    @11
    @31
    vx
    vy
    con0
    @9
    @29
    wceq
    @10
    @30
    cB
    @9
    @29
    cA
    coe
    oveq2
    eleq2d
    #
    cbvrabv
    #
    elrab2
    simprbi
    syl
    @53
    @49
    @3
    cX
    wlim
    #
    wa
    c0
    cA
    wcel
    #
    @4
    @54
    wceq
    @0
    @49
    @1
    @38
    @50
    ad2antrr
    @2
    @3
    @38
    @62
    @26
    @38
    @62
    @38
    @56
    @38
    @62
    wb
    @57
    @13
    cX
    limeq
    syl
    ibi
    anim12i
    @0
    @63
    @1
    @38
    cA
    dif20el
    ad2antrr
    vy
    cA
    cX
    con0
    oelim
    syl21anc
    eleqtrd
    vy
    cB
    cX
    @30
    eliun
    sylib
    @53
    @31
    vy
    cX
    @53
    @29
    cX
    wcel
    #
    wa
    @29
    con0
    wcel
    @29
    @13
    wcel
    #
    @31
    wn
    @53
    cX
    con0
    @29
    @53
    @3
    cX
    con0
    wss
    @2
    @3
    @38
    @26
    adantr
    cX
    onss
    syl
    sselda
    @53
    @65
    @64
    @53
    @13
    cX
    @29
    @58
    eleq2d
    biimpar
    @11
    @31
    vx
    @29
    @60
    onnminsb
    sylc
    nrexdv
    pm2.65da
    @37
    @38
    ioran
    sylanbrc
    @2
    @15
    @13
    word
    #
    @35
    @39
    wb
    @25
    @13
    eloni
    #
    @13
    unizlim
    3syl
    mtbird
    @2
    @35
    @36
    @2
    @15
    @66
    @35
    @36
    wo
    @25
    @67
    @13
    orduniorsuc
    3syl
    ord
    mpd
    cX
    @14
    wceq
    @6
    @34
    wceq
    oeeu.1
    cX
    @14
    suceq
    ax-mp
    syl6reqr
    #
    eleqtrd
    @12
    @32
    @61
    inteqi
    syl6eleq
    @31
    @27
    vy
    cX
    @59
    onnminsb
    sylc
    @2
    @4
    con0
    wcel
    #
    @21
    @5
    @28
    wb
    @2
    @49
    @3
    @69
    @51
    @26
    cA
    cX
    oecl
    syl2anc
    @22
    @4
    cB
    ontri1
    syl2anc
    mpbird
    @2
    @6
    @12
    wcel
    #
    @8
    @2
    @6
    @13
    @12
    @68
    @46
    eqeltrd
    @70
    @6
    con0
    wcel
    @8
    @31
    @8
    vy
    @6
    con0
    @12
    @29
    @6
    wceq
    @30
    @7
    cB
    @29
    @6
    cA
    coe
    oveq2
    eleq2d
    @61
    elrab2
    simprbi
    syl
    3jca
end
