include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cv.mm"
include "wrex.mm"
include "cif.mm"
include "cfz.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "a1i.mm"
include "wor.mm"
include "ltso.mm"
include "fzfid.mm"
include "cz.mm"
include "eluzelz2.mm"
include "syl.mm"
include "zred.mm"
include "leidd.mm"
include "cuz.mm"
include "cfv.mm"
include "syl6eleq.mm"
include "eluzle.mm"
include "elfzd.mm"
include "ne0d.mm"
include "fzssuz.mm"
include "eqcomi.mm"
include "sseqtri.mm"
include "id.mm"
include "sseldi.mm"
include "sylan2.mm"
include "fisupclrnmpt.mm"
include "eqeltrd.mm"
include "ifcld.mm"
include "syl5eqel.mm"
include "wa.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "ad2antlr.mm"
include "simpr.mm"
include "eluzd.mm"
include "rspa.mm"
include "syl2anc.mm"
include "max2.mm"
include "syl6breqr.mm"
include "letrd.mm"
include "wn.mm"
include "uzssre.mm"
include "eqsstri.mm"
include "sseli.mm"
include "ltnled.mm"
include "mpbird.mm"
include "syl5eqelr.mm"
include "simpll.mm"
include "cfzo.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "elfzod.mm"
include "elfzouz.mm"
include "3syl.mm"
include "ltled.mm"
include "cfn.mm"
include "ralrimia.mm"
include "fimaxre3.mm"
include "suprubrnmpt.mm"
include "max1.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "ex.mm"
include "ralrimi.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfeq.mm"
include "breq2.mm"
include "ralbid.mm"
include "rspce.mm"

theorem uzublem
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let vj: setvar j
  let cK: class K
  let cM: class M
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vy: setvar y
  assume uzublem.1: |- F/ j ph
  assume uzublem.2: |- F/_ j X
  assume uzublem.3: |- ( ph -> M e. ZZ )
  assume uzublem.4: |- Z = ( ZZ>= ` M )
  assume uzublem.5: |- ( ph -> Y e. RR )
  assume uzublem.6: |- W = sup ( ran ( j e. ( M ... K ) |-> B ) , RR , < )
  assume uzublem.7: |- X = if ( W <_ Y , Y , W )
  assume uzublem.8: |- ( ph -> K e. Z )
  assume uzublem.9: |- ( ( ph /\ j e. Z ) -> B e. RR )
  assume uzublem.10: |- ( ph -> A. j e. ( ZZ>= ` K ) B <_ Y )

  disjoint B x
  disjoint K j
  disjoint M j
  disjoint X x
  disjoint Z x
  disjoint j x
  disjoint B y
  disjoint K y
  disjoint j y
  disjoint M y
  assert |- ( ph -> E. x e. RR A. j e. Z B <_ x )

  proof
    wph
    cX
    cr
    wcel
    #
    cB
    cX
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    cB
    vx
    cv
    #
    cle
    wbr
    #
    vj
    cZ
    wral
    #
    vx
    cr
    wrex
    wph
    cX
    cW
    cY
    cle
    wbr
    #
    cY
    cW
    cif
    #
    cr
    uzublem.7
    wph
    @6
    cY
    cW
    cr
    uzublem.5
    wph
    cW
    vj
    cM
    cK
    cfz
    co
    #
    cB
    cmpt
    crn
    cr
    clt
    csup
    #
    cr
    cW
    @9
    wceq
    wph
    uzublem.6
    a1i
    wph
    vj
    cr
    @8
    cB
    clt
    uzublem.1
    cr
    clt
    wor
    wph
    ltso
    a1i
    wph
    cM
    cK
    fzfid
    #
    wph
    @8
    cM
    wph
    cM
    cM
    cK
    uzublem.3
    wph
    cK
    cZ
    wcel
    cK
    cz
    wcel
    #
    uzublem.8
    cM
    cK
    cZ
    uzublem.4
    eluzelz2
    syl
    #
    uzublem.3
    wph
    cM
    wph
    cM
    uzublem.3
    zred
    leidd
    wph
    cK
    cM
    cuz
    cfv
    #
    wcel
    cM
    cK
    cle
    wbr
    wph
    cK
    cZ
    @13
    uzublem.8
    uzublem.4
    syl6eleq
    cM
    cK
    eluzle
    syl
    elfzd
    ne0d
    vj
    cv
    #
    @8
    wcel
    #
    wph
    @14
    cZ
    wcel
    #
    cB
    cr
    wcel
    #
    @15
    @8
    cZ
    @14
    @8
    @13
    cZ
    cM
    cK
    fzssuz
    cZ
    @13
    uzublem.4
    eqcomi
    #
    sseqtri
    @15
    id
    sseldi
    uzublem.9
    sylan2
    #
    fisupclrnmpt
    eqeltrd
    #
    ifcld
    syl5eqel
    #
    wph
    @1
    vj
    cZ
    uzublem.1
    wph
    @16
    @1
    wph
    @16
    wa
    #
    cK
    @14
    cle
    wbr
    #
    @1
    @22
    @23
    wa
    #
    cB
    cY
    cX
    @22
    @17
    @23
    uzublem.9
    adantr
    wph
    cY
    cr
    wcel
    #
    @16
    @23
    uzublem.5
    ad2antrr
    wph
    @0
    @16
    @23
    @21
    ad2antrr
    @24
    cB
    cY
    cle
    wbr
    #
    vj
    cK
    cuz
    cfv
    #
    wral
    #
    @14
    @27
    wcel
    @26
    wph
    @28
    @16
    @23
    uzublem.10
    ad2antrr
    @24
    cK
    @14
    @27
    @27
    eqid
    wph
    @11
    @16
    @23
    @12
    ad2antrr
    @16
    @14
    cz
    wcel
    #
    wph
    @23
    cM
    @14
    cZ
    uzublem.4
    eluzelz2
    #
    ad2antlr
    @22
    @23
    simpr
    eluzd
    @26
    vj
    @27
    rspa
    syl2anc
    wph
    cY
    cX
    cle
    wbr
    @16
    @23
    wph
    cY
    @7
    cX
    cle
    wph
    cW
    cr
    wcel
    #
    @25
    cY
    @7
    cle
    wbr
    @20
    uzublem.5
    cW
    cY
    max2
    syl2anc
    uzublem.7
    syl6breqr
    ad2antrr
    letrd
    @22
    @23
    wn
    #
    @14
    cK
    clt
    wbr
    #
    @1
    @22
    @32
    wa
    #
    @33
    @32
    @22
    @32
    simpr
    @34
    @14
    cK
    @16
    @14
    cr
    wcel
    #
    wph
    @32
    cZ
    cr
    @14
    cZ
    @13
    cr
    uzublem.4
    cM
    uzssre
    eqsstri
    #
    sseli
    #
    ad2antlr
    wph
    cK
    cr
    wcel
    #
    @16
    @32
    wph
    cZ
    cr
    cK
    @36
    uzublem.8
    sseldi
    #
    ad2antrr
    ltnled
    mpbird
    @22
    @33
    wa
    #
    cB
    cW
    cX
    @22
    @17
    @33
    uzublem.9
    adantr
    wph
    @31
    @16
    @33
    wph
    cW
    @9
    cr
    uzublem.6
    wph
    @9
    cW
    cr
    uzublem.6
    @20
    syl5eqelr
    syl5eqel
    #
    ad2antrr
    wph
    @0
    @16
    @33
    wph
    cX
    @7
    cr
    uzublem.7
    wph
    @6
    cY
    cW
    cr
    uzublem.5
    @41
    ifcld
    syl5eqel
    ad2antrr
    @40
    cB
    @9
    cW
    cle
    @40
    wph
    @15
    cB
    @9
    cle
    wbr
    wph
    @16
    @33
    simpll
    @40
    @14
    cM
    cK
    wph
    cM
    cz
    wcel
    @16
    @33
    uzublem.3
    ad2antrr
    wph
    @11
    @16
    @33
    @12
    ad2antrr
    #
    @40
    @14
    cM
    cK
    cfzo
    co
    wcel
    #
    @16
    @29
    @40
    @14
    cM
    cK
    @16
    @14
    @13
    wcel
    #
    wph
    @33
    @16
    @44
    cZ
    @13
    @14
    uzublem.4
    eleq2i
    biimpi
    #
    ad2antlr
    @42
    @22
    @33
    simpr
    #
    elfzod
    #
    @43
    @14
    @13
    cZ
    @14
    cM
    cK
    elfzouz
    @18
    syl6eleq
    #
    @30
    3syl
    @16
    cM
    @14
    cle
    wbr
    #
    wph
    @33
    @16
    @44
    @49
    @45
    cM
    @14
    eluzle
    syl
    ad2antlr
    @40
    @14
    cK
    @40
    @43
    @16
    @35
    @47
    @48
    @37
    3syl
    wph
    @38
    @16
    @33
    @39
    ad2antrr
    @46
    ltled
    elfzd
    wph
    vj
    vy
    @8
    cB
    uzublem.1
    @19
    wph
    @8
    cfn
    wcel
    @17
    vj
    @8
    wral
    cB
    vy
    cv
    cle
    wbr
    vj
    @8
    wral
    vy
    cr
    wrex
    @10
    wph
    @17
    vj
    @8
    uzublem.1
    @19
    ralrimia
    vy
    vj
    @8
    cB
    fimaxre3
    syl2anc
    suprubrnmpt
    syl2anc
    uzublem.6
    syl6breqr
    wph
    cW
    cX
    cle
    wbr
    @16
    @33
    wph
    cW
    @7
    cX
    cle
    wph
    @31
    @25
    cW
    @7
    cle
    wbr
    @20
    uzublem.5
    cW
    cY
    max1
    syl2anc
    uzublem.7
    syl6breqr
    ad2antrr
    letrd
    syldan
    pm2.61dan
    ex
    ralrimi
    @5
    @2
    vx
    cX
    cr
    @2
    vx
    nfv
    @3
    cX
    wceq
    @4
    @1
    vj
    cZ
    vj
    @3
    cX
    vj
    @3
    nfcv
    uzublem.2
    nfeq
    @3
    cX
    cB
    cle
    breq2
    ralbid
    rspce
    syl2anc
end
