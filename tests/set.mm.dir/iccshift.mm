include "cv.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cicc.mm"
include "wrex.mm"
include "cc.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elrab.mm"
include "simprr.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "wi.mm"
include "w3a.mm"
include "simp3.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "iccssred.mm"
include "sselda.mm"
include "adantr.mm"
include "readdcld.mm"
include "simpr.mm"
include "wb.mm"
include "elicc2.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simp2d.mm"
include "leadd1dd.mm"
include "simp3d.mm"
include "3jca.mm"
include "3adant3.mm"
include "3ad2ant1.mm"
include "mpbird.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "sylan2b.mm"
include "eliccre.mm"
include "syl3anc.mm"
include "recnd.mm"
include "cmin.mm"
include "resubcld.mm"
include "pncand.mm"
include "eqcomd.mm"
include "lesub1dd.mm"
include "eqbrtrd.mm"
include "breqtrd.mm"
include "eliccd.mm"
include "npcand.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "sylanbrc.mm"
include "impbida.mm"
include "eqrdv.mm"

theorem iccshift
  let wph: wff ph
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cT: class T
  let vx: setvar x
  assume iccshift.1: |- ( ph -> A e. RR )
  assume iccshift.2: |- ( ph -> B e. RR )
  assume iccshift.3: |- ( ph -> T e. RR )

  disjoint A w
  disjoint A z
  disjoint w z
  disjoint B w
  disjoint B z
  disjoint T w
  disjoint T z
  disjoint ph z
  disjoint A x
  disjoint w x
  disjoint x z
  disjoint B x
  disjoint T x
  disjoint ph x
  assert |- ( ph -> ( ( A + T ) [,] ( B + T ) ) = { w e. CC | E. z e. ( A [,] B ) w = ( z + T ) } )

  proof
    wph
    vw
    cv
    #
    vz
    cv
    #
    cT
    caddc
    co
    #
    wceq
    #
    vz
    cA
    cB
    cicc
    co
    #
    wrex
    #
    vw
    cc
    crab
    #
    cA
    cT
    caddc
    co
    #
    cB
    cT
    caddc
    co
    #
    cicc
    co
    #
    wph
    vx
    @6
    @9
    wph
    vx
    cv
    #
    @6
    wcel
    #
    @10
    @9
    wcel
    #
    @11
    wph
    @10
    cc
    wcel
    #
    @10
    @2
    wceq
    #
    vz
    @4
    wrex
    #
    wa
    #
    @12
    @5
    @15
    vw
    @10
    cc
    @0
    @10
    wceq
    @3
    @14
    vz
    @4
    @0
    @10
    @2
    eqeq1
    rexbidv
    elrab
    #
    wph
    @16
    wa
    #
    @15
    @12
    wph
    @13
    @15
    simprr
    @18
    @14
    @12
    vz
    @4
    wph
    @16
    vz
    wph
    vz
    nfv
    @13
    @15
    vz
    @13
    vz
    nfv
    @14
    vz
    @4
    nfre1
    nfan
    nfan
    @12
    vz
    nfv
    wph
    @1
    @4
    wcel
    #
    @14
    @12
    wi
    wi
    @16
    wph
    @19
    @14
    @12
    wph
    @19
    @14
    w3a
    #
    @10
    @2
    @9
    wph
    @19
    @14
    simp3
    @20
    @2
    @9
    wcel
    #
    @2
    cr
    wcel
    #
    @7
    @2
    cle
    wbr
    #
    @2
    @8
    cle
    wbr
    #
    w3a
    #
    wph
    @19
    @25
    @14
    wph
    @19
    wa
    #
    @22
    @23
    @24
    @26
    @1
    cT
    wph
    @4
    cr
    @1
    wph
    cA
    cB
    iccshift.1
    iccshift.2
    iccssred
    sselda
    #
    wph
    cT
    cr
    wcel
    #
    @19
    iccshift.3
    adantr
    #
    readdcld
    @26
    cA
    @1
    cT
    wph
    cA
    cr
    wcel
    #
    @19
    iccshift.1
    adantr
    #
    @27
    @29
    @26
    @1
    cr
    wcel
    #
    cA
    @1
    cle
    wbr
    #
    @1
    cB
    cle
    wbr
    #
    @26
    @19
    @32
    @33
    @34
    w3a
    #
    wph
    @19
    simpr
    @26
    @30
    cB
    cr
    wcel
    #
    @19
    @35
    wb
    @31
    wph
    @36
    @19
    iccshift.2
    adantr
    #
    cA
    cB
    @1
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    leadd1dd
    @26
    @1
    cB
    cT
    @27
    @37
    @29
    @26
    @32
    @33
    @34
    @38
    simp3d
    leadd1dd
    3jca
    3adant3
    @20
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    #
    @21
    @25
    wb
    wph
    @19
    @39
    @14
    wph
    cA
    cT
    iccshift.1
    iccshift.3
    readdcld
    #
    3ad2ant1
    wph
    @19
    @40
    @14
    wph
    cB
    cT
    iccshift.2
    iccshift.3
    readdcld
    #
    3ad2ant1
    @7
    @8
    @2
    elicc2
    syl2anc
    mpbird
    eqeltrd
    3exp
    adantr
    rexlimd
    mpd
    sylan2b
    wph
    @12
    wa
    #
    @13
    @15
    @11
    @43
    @10
    @43
    @39
    @40
    @12
    @10
    cr
    wcel
    #
    wph
    @39
    @12
    @41
    adantr
    #
    wph
    @40
    @12
    @42
    adantr
    #
    wph
    @12
    simpr
    #
    @7
    @8
    @10
    eliccre
    syl3anc
    #
    recnd
    #
    @43
    @10
    cT
    cmin
    co
    #
    @4
    wcel
    @10
    @50
    cT
    caddc
    co
    #
    wceq
    #
    @15
    @43
    cA
    cB
    @50
    wph
    @30
    @12
    iccshift.1
    adantr
    wph
    @36
    @12
    iccshift.2
    adantr
    @43
    @10
    cT
    @48
    wph
    @28
    @12
    iccshift.3
    adantr
    #
    resubcld
    @43
    cA
    @7
    cT
    cmin
    co
    #
    @50
    cle
    wph
    cA
    @54
    wceq
    @12
    wph
    @54
    cA
    wph
    cA
    cT
    wph
    cA
    iccshift.1
    recnd
    wph
    cT
    iccshift.3
    recnd
    #
    pncand
    eqcomd
    adantr
    @43
    @7
    @10
    cT
    @45
    @48
    @53
    @43
    @44
    @7
    @10
    cle
    wbr
    #
    @10
    @8
    cle
    wbr
    #
    @43
    @12
    @44
    @56
    @57
    w3a
    #
    @47
    @43
    @39
    @40
    @12
    @58
    wb
    @45
    @46
    @7
    @8
    @10
    elicc2
    syl2anc
    mpbid
    #
    simp2d
    lesub1dd
    eqbrtrd
    @43
    @50
    @8
    cT
    cmin
    co
    #
    cB
    cle
    @43
    @10
    @8
    cT
    @48
    @46
    @53
    @43
    @44
    @56
    @57
    @59
    simp3d
    lesub1dd
    wph
    @60
    cB
    wceq
    @12
    wph
    cB
    cT
    wph
    cB
    iccshift.2
    recnd
    @55
    pncand
    adantr
    breqtrd
    eliccd
    @43
    @51
    @10
    @43
    @10
    cT
    @49
    wph
    cT
    cc
    wcel
    @12
    @55
    adantr
    npcand
    eqcomd
    @14
    @52
    vz
    @50
    @4
    @1
    @50
    wceq
    @2
    @51
    @10
    @1
    @50
    cT
    caddc
    oveq1
    eqeq2d
    rspcev
    syl2anc
    @17
    sylanbrc
    impbida
    eqrdv
    eqcomd
end
