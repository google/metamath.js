include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cdmd.mm"
include "wbr.mm"
include "cv.mm"
include "chj.mm"
include "co.mm"
include "wss.mm"
include "cin.mm"
include "wi.mm"
include "wral.mm"
include "dmdbr4.mm"
include "chub1.mm"
include "ancoms.mm"
include "ssin.mm"
include "sstr2.mm"
include "sylbi.mm"
include "sylan.mm"
include "ex.mm"
include "com23.mm"
include "ralimdva.mm"
include "adantl.mm"
include "sylbid.mm"
include "wceq.mm"
include "sseq1.mm"
include "id.mm"
include "oveq1.mm"
include "ineq1d.mm"
include "oveq1d.mm"
include "sseq12d.mm"
include "imbi12d.mm"
include "rspccv.mm"
include "chjcl.mm"
include "adantll.mm"
include "adantr.mm"
include "chincl.mm"
include "syl2anc.mm"
include "inss2.mm"
include "pm2.27.mm"
include "mpii.mm"
include "syl.mm"
include "chub2.mm"
include "ssind.mm"
include "wb.mm"
include "simplr.mm"
include "chlejb2.mm"
include "mpbid.mm"
include "inass.mm"
include "incom.mm"
include "chabs2.mm"
include "syl5eq.mm"
include "ineq2d.mm"
include "eqtrd.mm"
include "sseq2d.mm"
include "sylibd.mm"
include "syl5.mm"
include "ralrimdv.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem dmdbr5
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let cC: class C

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  disjoint C x
  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH* B <-> A. x e. CH ( x C_ ( A vH B ) -> x C_ ( ( ( x vH B ) i^i A ) vH B ) ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cA
    cB
    cdmd
    wbr
    #
    vx
    cv
    #
    cA
    cB
    chj
    co
    #
    wss
    #
    @4
    @4
    cB
    chj
    co
    #
    cA
    cin
    #
    cB
    chj
    co
    #
    wss
    #
    wi
    #
    vx
    cch
    wral
    #
    @2
    @3
    @7
    @5
    cin
    #
    @9
    wss
    #
    vx
    cch
    wral
    #
    @12
    vx
    cA
    cB
    dmdbr4
    @1
    @15
    @12
    wi
    @0
    @1
    @14
    @11
    vx
    cch
    @1
    @4
    cch
    wcel
    #
    wa
    #
    @6
    @14
    @10
    @17
    @6
    @14
    @10
    wi
    #
    @17
    @4
    @7
    wss
    #
    @6
    @18
    @16
    @1
    @19
    @4
    cB
    chub1
    ancoms
    @19
    @6
    wa
    @4
    @13
    wss
    @18
    @4
    @7
    @5
    ssin
    @4
    @13
    @9
    sstr2
    sylbi
    sylan
    ex
    com23
    ralimdva
    adantl
    sylbid
    @2
    @12
    vy
    cv
    #
    cB
    chj
    co
    #
    @5
    cin
    #
    @21
    cA
    cin
    #
    cB
    chj
    co
    #
    wss
    #
    vy
    cch
    wral
    @3
    @2
    @12
    @25
    vy
    cch
    @12
    @22
    cch
    wcel
    #
    @22
    @5
    wss
    #
    @22
    @22
    cB
    chj
    co
    #
    cA
    cin
    #
    cB
    chj
    co
    #
    wss
    #
    wi
    #
    wi
    #
    @2
    @20
    cch
    wcel
    #
    @25
    wi
    @11
    @32
    vx
    @22
    cch
    @4
    @22
    wceq
    #
    @6
    @27
    @10
    @31
    @4
    @22
    @5
    sseq1
    @35
    @4
    @22
    @9
    @30
    @35
    id
    @35
    @8
    @29
    cB
    chj
    @35
    @7
    @28
    cA
    @4
    @22
    cB
    chj
    oveq1
    ineq1d
    oveq1d
    sseq12d
    imbi12d
    rspccv
    @2
    @34
    @33
    @25
    @2
    @34
    @33
    @25
    wi
    @2
    @34
    wa
    #
    @33
    @31
    @25
    @36
    @26
    @33
    @31
    wi
    @36
    @21
    cch
    wcel
    #
    @5
    cch
    wcel
    #
    @26
    @1
    @34
    @37
    @0
    @34
    @1
    @37
    @20
    cB
    chjcl
    ancoms
    adantll
    @2
    @38
    @34
    cA
    cB
    chjcl
    adantr
    @21
    @5
    chincl
    syl2anc
    #
    @26
    @33
    @27
    @31
    @21
    @5
    inss2
    @26
    @32
    pm2.27
    mpii
    syl
    @36
    @30
    @24
    @22
    @36
    @29
    @23
    cB
    chj
    @36
    @29
    @22
    cA
    cin
    #
    @23
    @36
    @28
    @22
    cA
    @36
    cB
    @22
    wss
    #
    @28
    @22
    wceq
    #
    @36
    cB
    @21
    @5
    @1
    @34
    cB
    @21
    wss
    @0
    cB
    @20
    chub2
    adantll
    @2
    cB
    @5
    wss
    #
    @34
    @1
    @0
    @43
    cB
    cA
    chub2
    ancoms
    adantr
    ssind
    @36
    @1
    @26
    @41
    @42
    wb
    @0
    @1
    @34
    simplr
    @39
    cB
    @22
    chlejb2
    syl2anc
    mpbid
    ineq1d
    @2
    @40
    @23
    wceq
    @34
    @2
    @40
    @21
    @5
    cA
    cin
    #
    cin
    @23
    @21
    @5
    cA
    inass
    @2
    @44
    cA
    @21
    @2
    @44
    cA
    @5
    cin
    cA
    @5
    cA
    incom
    cA
    cB
    chabs2
    syl5eq
    ineq2d
    syl5eq
    adantr
    eqtrd
    oveq1d
    sseq2d
    sylibd
    ex
    com23
    syl5
    ralrimdv
    vy
    cA
    cB
    dmdbr4
    sylibrd
    impbid
end
