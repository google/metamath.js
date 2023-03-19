include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wa.mm"
include "wcel.mm"
include "w3a.mm"
include "simp2.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "3ad2antl1.mm"
include "cc.mm"
include "recnd.mm"
include "abscld.mm"
include "adantr.mm"
include "leabsd.mm"
include "rspa.mm"
include "3ad2antl3.mm"
include "letrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cneg.mm"
include "renegcld.mm"
include "wb.mm"
include "adantlr.mm"
include "simplr.mm"
include "absle.mm"
include "3adantl3.mm"
include "mpbid.mm"
include "simpld.mm"
include "breq1.mm"
include "jca.mm"
include "3exp.mm"
include "rexlimdv.mm"
include "wi.mm"
include "cif.mm"
include "renegcl.mm"
include "adantl.mm"
include "simpl.mm"
include "ifcld.mm"
include "ad5ant24.mm"
include "nfan.mm"
include "ad5ant23.mm"
include "simpllr.mm"
include "ad5ant15.mm"
include "max2.mm"
include "lenegd.mm"
include "recn.mm"
include "negnegd.mm"
include "breqtrd.mm"
include "adantll.mm"
include "ad5ant1345.mm"
include "simp-4r.mm"
include "ad4ant24.mm"
include "max1.mm"
include "3adant2.mm"
include "3adant3.mm"
include "absled.mm"
include "ad5ant135.mm"
include "mpbird.mm"
include "exp31.mm"
include "imp.mm"
include "anasss.mm"
include "impbid.mm"

theorem rexabslelem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  assume rexabslelem.1: |- F/ x ph
  assume rexabslelem.2: |- ( ( ph /\ x e. A ) -> B e. RR )

  disjoint A w
  disjoint A y
  disjoint A z
  disjoint w y
  disjoint w z
  disjoint y z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint ph w
  disjoint ph y
  disjoint ph z
  disjoint w x
  disjoint x y
  disjoint x z
  assert |- ( ph -> ( E. y e. RR A. x e. A ( abs ` B ) <_ y <-> ( E. w e. RR A. x e. A B <_ w /\ E. z e. RR A. x e. A z <_ B ) ) )

  proof
    wph
    cB
    cabs
    cfv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vy
    cr
    wrex
    #
    cB
    vw
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vw
    cr
    wrex
    #
    vz
    cv
    #
    cB
    cle
    wbr
    #
    vx
    cA
    wral
    #
    vz
    cr
    wrex
    #
    wa
    #
    wph
    @3
    @13
    vy
    cr
    wph
    @1
    cr
    wcel
    #
    @3
    @13
    wph
    @14
    @3
    w3a
    #
    @8
    @12
    @15
    @14
    cB
    @1
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @8
    wph
    @14
    @3
    simp2
    #
    @15
    @16
    vx
    cA
    wph
    @14
    @3
    vx
    rexabslelem.1
    @14
    vx
    nfv
    @2
    vx
    cA
    nfra1
    nf3an
    #
    @15
    vx
    cv
    cA
    wcel
    #
    @16
    @15
    @20
    wa
    #
    cB
    @0
    @1
    wph
    @14
    @20
    cB
    cr
    wcel
    #
    @3
    rexabslelem.2
    3ad2antl1
    #
    @21
    cB
    wph
    @14
    @20
    cB
    cc
    wcel
    @3
    wph
    @20
    wa
    cB
    rexabslelem.2
    recnd
    3ad2antl1
    abscld
    @15
    @14
    @20
    @18
    adantr
    @21
    cB
    @23
    leabsd
    @3
    wph
    @20
    @2
    @14
    @2
    vx
    cA
    rspa
    3ad2antl3
    #
    letrd
    ex
    ralrimi
    @7
    @17
    vw
    @1
    cr
    @5
    @1
    wceq
    @6
    @16
    vx
    cA
    @5
    @1
    cB
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    @15
    @1
    cneg
    #
    cr
    wcel
    @25
    cB
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @12
    @15
    @1
    @18
    renegcld
    @15
    @26
    vx
    cA
    @19
    @15
    @20
    @26
    @21
    @26
    @16
    @21
    @2
    @26
    @16
    wa
    #
    @24
    wph
    @14
    @20
    @2
    @28
    wb
    #
    @3
    wph
    @14
    wa
    @20
    wa
    @22
    @14
    @29
    wph
    @20
    @22
    @14
    rexabslelem.2
    adantlr
    wph
    @14
    @20
    simplr
    cB
    @1
    absle
    syl2anc
    3adantl3
    mpbid
    simpld
    ex
    ralrimi
    @11
    @27
    vz
    @25
    cr
    @9
    @25
    wceq
    @10
    @26
    vx
    cA
    @9
    @25
    cB
    cle
    breq1
    ralbidv
    rspcev
    syl2anc
    jca
    3exp
    rexlimdv
    wph
    @13
    @4
    wph
    @8
    @12
    @4
    wph
    @8
    wa
    #
    @12
    @4
    @30
    @11
    @4
    vz
    cr
    wph
    @8
    @9
    cr
    wcel
    #
    @11
    @4
    wi
    wi
    #
    wph
    @7
    @32
    vw
    cr
    wph
    @5
    cr
    wcel
    #
    @7
    @32
    wph
    @33
    wa
    #
    @7
    wa
    #
    @31
    @11
    @4
    @35
    @31
    wa
    #
    @11
    wa
    #
    @5
    @9
    cneg
    #
    cle
    wbr
    #
    @38
    @5
    cif
    #
    cr
    wcel
    #
    @0
    @40
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @4
    @33
    @31
    @41
    wph
    @7
    @11
    @33
    @31
    wa
    #
    @39
    @38
    @5
    cr
    @31
    @38
    cr
    wcel
    #
    @33
    @9
    renegcl
    adantl
    #
    @33
    @31
    simpl
    #
    ifcld
    #
    ad5ant24
    @37
    @42
    vx
    cA
    @36
    @11
    vx
    @35
    @31
    vx
    @34
    @7
    vx
    wph
    @33
    vx
    rexabslelem.1
    @33
    vx
    nfv
    nfan
    @6
    vx
    cA
    nfra1
    nfan
    @31
    vx
    nfv
    nfan
    @10
    vx
    cA
    nfra1
    nfan
    @37
    @20
    @42
    @37
    @20
    wa
    #
    @42
    @40
    cneg
    #
    cB
    cle
    wbr
    #
    cB
    @40
    cle
    wbr
    #
    wa
    #
    @49
    @51
    @52
    @34
    @31
    @11
    @20
    @51
    @7
    @34
    @31
    wa
    #
    @11
    wa
    @20
    wa
    #
    @50
    @9
    cB
    @55
    @40
    @33
    @31
    @41
    wph
    @11
    @20
    @48
    ad5ant23
    renegcld
    @34
    @31
    @11
    @20
    simpllr
    wph
    @20
    @22
    @33
    @31
    @11
    rexabslelem.2
    ad5ant15
    @33
    @31
    @50
    @9
    cle
    wbr
    wph
    @11
    @20
    @44
    @50
    @38
    cneg
    #
    @9
    cle
    @44
    @38
    @40
    cle
    wbr
    #
    @50
    @56
    cle
    wbr
    @44
    @33
    @45
    @57
    @47
    @46
    @5
    @38
    max2
    syl2anc
    @44
    @38
    @40
    @46
    @48
    lenegd
    mpbid
    @44
    @9
    @31
    @9
    cc
    wcel
    @33
    @9
    recn
    adantl
    negnegd
    breqtrd
    ad5ant23
    @11
    @20
    @10
    @54
    @10
    vx
    cA
    rspa
    adantll
    letrd
    ad5ant1345
    @36
    @20
    @52
    @11
    @36
    @20
    wa
    cB
    @5
    @40
    wph
    @20
    @22
    @33
    @7
    @31
    rexabslelem.2
    ad5ant15
    wph
    @33
    @7
    @31
    @20
    simp-4r
    @33
    @31
    @41
    wph
    @7
    @20
    @48
    ad5ant24
    @7
    @20
    @6
    @34
    @31
    @6
    vx
    cA
    rspa
    ad4ant24
    @33
    @31
    @5
    @40
    cle
    wbr
    #
    wph
    @7
    @20
    @44
    @33
    @45
    @58
    @47
    @46
    @5
    @38
    max1
    syl2anc
    ad5ant24
    letrd
    adantlr
    jca
    @34
    @31
    @20
    @42
    @53
    wb
    @7
    @11
    @34
    @31
    @20
    w3a
    cB
    @40
    @34
    @20
    @22
    @31
    wph
    @20
    @22
    @33
    rexabslelem.2
    adantlr
    3adant2
    @34
    @31
    @41
    @20
    @33
    @31
    @41
    wph
    @48
    adantll
    3adant3
    absled
    ad5ant135
    mpbird
    ex
    ralrimi
    @3
    @43
    vy
    @40
    cr
    @1
    @40
    wceq
    @2
    @42
    vx
    cA
    @1
    @40
    @0
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    exp31
    exp31
    rexlimdv
    imp
    rexlimdv
    imp
    anasss
    ex
    impbid
end
