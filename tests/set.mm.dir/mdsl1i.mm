include "cin.mm"
include "cv.mm"
include "wss.mm"
include "chj.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "cch.mm"
include "wral.mm"
include "cmd.mm"
include "wbr.mm"
include "wcel.mm"
include "sseq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "impexp.mm"
include "bitr2i.mm"
include "inss2.mm"
include "wb.mm"
include "chincli.mm"
include "chlub.mm"
include "mp3an23.mm"
include "biimpd.mm"
include "mpan2i.mm"
include "chub2i.mm"
include "sstr.mm"
include "mpan2.mm"
include "syl6.mm"
include "chub2.mm"
include "mpan.mm"
include "jctild.mm"
include "chjcl.mm"
include "jcad.mm"
include "chjass.mm"
include "chjcomi.mm"
include "chabs1i.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "chjidmi.mm"
include "imim12d.mm"
include "syl5bi.mm"
include "syl5com.mm"
include "ralrimiv.mm"
include "mdbr.mm"
include "mp2an.mm"
include "sylibr.mm"
include "ax-1.mm"
include "ralimi.mm"
include "sylbi.mm"
include "impbii.mm"

theorem mdsl1i
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  assume mdsl.1: |- A e. CH
  assume mdsl.2: |- B e. CH

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( A. x e. CH ( ( ( A i^i B ) C_ x /\ x C_ ( A vH B ) ) -> ( x C_ B -> ( ( x vH A ) i^i B ) = ( x vH ( A i^i B ) ) ) ) <-> A MH B )

  proof
    cA
    cB
    cin
    #
    vx
    cv
    #
    wss
    #
    @1
    cA
    cB
    chj
    co
    #
    wss
    #
    wa
    #
    @1
    cB
    wss
    #
    @1
    cA
    chj
    co
    #
    cB
    cin
    #
    @1
    @0
    chj
    co
    #
    wceq
    #
    wi
    #
    wi
    #
    vx
    cch
    wral
    #
    cA
    cB
    cmd
    wbr
    #
    @13
    vy
    cv
    #
    cB
    wss
    #
    @15
    cA
    chj
    co
    #
    cB
    cin
    #
    @15
    @0
    chj
    co
    #
    wceq
    #
    wi
    #
    vy
    cch
    wral
    #
    @14
    @13
    @21
    vy
    cch
    @13
    @19
    cch
    wcel
    #
    @0
    @19
    wss
    #
    @19
    @3
    wss
    #
    wa
    #
    @19
    cB
    wss
    #
    @19
    cA
    chj
    co
    #
    cB
    cin
    #
    @19
    @0
    chj
    co
    #
    wceq
    #
    wi
    #
    wi
    #
    wi
    #
    @15
    cch
    wcel
    #
    @21
    @12
    @33
    vx
    @19
    cch
    @1
    @19
    wceq
    #
    @5
    @26
    @11
    @32
    @36
    @2
    @24
    @4
    @25
    @1
    @19
    @0
    sseq2
    @1
    @19
    @3
    sseq1
    anbi12d
    @36
    @6
    @27
    @10
    @31
    @1
    @19
    cB
    sseq1
    @36
    @8
    @29
    @9
    @30
    @36
    @7
    @28
    cB
    @1
    @19
    cA
    chj
    oveq1
    ineq1d
    @1
    @19
    @0
    chj
    oveq1
    eqeq12d
    imbi12d
    imbi12d
    rspccv
    @34
    @23
    @26
    wa
    #
    @27
    wa
    #
    @31
    wi
    #
    @35
    @21
    @39
    @37
    @32
    wi
    @34
    @37
    @27
    @31
    impexp
    @23
    @26
    @32
    impexp
    bitr2i
    @35
    @16
    @38
    @31
    @20
    @35
    @16
    @37
    @27
    @35
    @16
    @26
    @23
    @35
    @16
    @25
    @24
    @35
    @16
    @27
    @25
    @35
    @16
    @0
    cB
    wss
    #
    @27
    cA
    cB
    inss2
    @35
    @16
    @40
    wa
    #
    @27
    @35
    @0
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    @41
    @27
    wb
    cA
    cB
    mdsl.1
    mdsl.2
    chincli
    #
    mdsl.2
    @15
    @0
    cB
    chlub
    mp3an23
    biimpd
    mpan2i
    #
    @27
    cB
    @3
    wss
    @25
    cB
    cA
    mdsl.2
    mdsl.1
    chub2i
    @19
    cB
    @3
    sstr
    mpan2
    syl6
    @42
    @35
    @24
    @44
    @0
    @15
    chub2
    mpan
    jctild
    @35
    @42
    @23
    @44
    @15
    @0
    chjcl
    mpan2
    jctild
    @45
    jcad
    @35
    @31
    @20
    @35
    @29
    @18
    @30
    @19
    @35
    @28
    @17
    cB
    @35
    @28
    @15
    @0
    cA
    chj
    co
    #
    chj
    co
    #
    @17
    @35
    @42
    cA
    cch
    wcel
    #
    @28
    @47
    wceq
    @44
    mdsl.1
    @15
    @0
    cA
    chjass
    mp3an23
    @46
    cA
    @15
    chj
    @46
    cA
    @0
    chj
    co
    cA
    @0
    cA
    @44
    mdsl.1
    chjcomi
    cA
    cB
    mdsl.1
    mdsl.2
    chabs1i
    eqtri
    oveq2i
    syl6eq
    ineq1d
    @35
    @30
    @15
    @0
    @0
    chj
    co
    #
    chj
    co
    #
    @19
    @35
    @42
    @42
    @30
    @50
    wceq
    @44
    @44
    @15
    @0
    @0
    chjass
    mp3an23
    @49
    @0
    @15
    chj
    @0
    @44
    chjidmi
    oveq2i
    syl6eq
    eqeq12d
    biimpd
    imim12d
    syl5bi
    syl5com
    ralrimiv
    @48
    @43
    @14
    @22
    wb
    mdsl.1
    mdsl.2
    vy
    cA
    cB
    mdbr
    mp2an
    sylibr
    @14
    @11
    vx
    cch
    wral
    #
    @13
    @48
    @43
    @14
    @51
    wb
    mdsl.1
    mdsl.2
    vx
    cA
    cB
    mdbr
    mp2an
    @11
    @12
    vx
    cch
    @11
    @5
    ax-1
    ralimi
    sylbi
    impbii
end
