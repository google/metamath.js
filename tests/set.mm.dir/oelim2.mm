include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "coe.mm"
include "co.mm"
include "c1o.mm"
include "cdif.mm"
include "cv.mm"
include "ciun.mm"
include "wceq.mm"
include "c0.mm"
include "con0.mm"
include "limelon.mm"
include "0ellim.mm"
include "adantl.mm"
include "oe0m1.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "wn.mm"
include "eldif.mm"
include "wi.mm"
include "word.mm"
include "limord.mm"
include "ordelon.mm"
include "sylan.mm"
include "wne.mm"
include "on0eln0.mm"
include "el1o.mm"
include "necon3bbii.mm"
include "syl6bbr.mm"
include "biimpd.mm"
include "sylbird.mm"
include "syl.mm"
include "impr.mm"
include "sylan2b.mm"
include "iuneq2dv.mm"
include "csuc.mm"
include "df-1o.mm"
include "limsuc.mm"
include "mpbid.mm"
include "syl5eqel.mm"
include "1on.mm"
include "onirri.mm"
include "jctir.mm"
include "sylibr.mm"
include "ne0i.mm"
include "iunconst.mm"
include "3syl.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "eqeq12d.mm"
include "syl5ibr.mm"
include "impcom.mm"
include "oelim.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "nsuceq0.mm"
include "a1i.mm"
include "dif1o.mm"
include "sylanbrc.mm"
include "ex.mm"
include "ad2antlr.mm"
include "sssucid.mm"
include "w3a.mm"
include "suceloni.mm"
include "jccir.mm"
include "id.mm"
include "3expa.mm"
include "ancoms.mm"
include "sylan2.mm"
include "anassrs.mm"
include "oewordi.mm"
include "an32s.mm"
include "mpi.mm"
include "jcad.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "syl6.mm"
include "ralrimiv.mm"
include "iunss2.mm"
include "difss.mm"
include "iunss1.mm"
include "ax-mp.mm"
include "cbviunv.mm"
include "sseqtri.mm"
include "eqssd.mm"
include "adantlrl.mm"
include "oe0lem.mm"

theorem oelim2
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  disjoint C y
  assert |- ( ( A e. On /\ ( B e. C /\ Lim B ) ) -> ( A ^o B ) = U_ x e. ( B \ 1o ) ( A ^o x ) )

  proof
    cB
    cC
    wcel
    #
    cB
    wlim
    #
    wa
    #
    cA
    cB
    coe
    co
    #
    vx
    cB
    c1o
    cdif
    #
    cA
    vx
    cv
    #
    coe
    co
    #
    ciun
    #
    wceq
    #
    cA
    cA
    c0
    wceq
    #
    @2
    @8
    @2
    @8
    @9
    c0
    cB
    coe
    co
    #
    vx
    @4
    c0
    @5
    coe
    co
    #
    ciun
    #
    wceq
    @2
    @10
    c0
    @12
    @2
    cB
    con0
    wcel
    #
    c0
    cB
    wcel
    #
    @10
    c0
    wceq
    #
    cB
    cC
    limelon
    @1
    @14
    @0
    cB
    0ellim
    #
    adantl
    @13
    @14
    @15
    cB
    oe0m1
    biimpa
    syl2anc
    @1
    @12
    c0
    wceq
    @0
    @1
    @12
    vx
    @4
    c0
    ciun
    #
    c0
    @1
    vx
    @4
    @11
    c0
    @5
    @4
    wcel
    @1
    @5
    cB
    wcel
    #
    @5
    c1o
    wcel
    #
    wn
    #
    wa
    @11
    c0
    wceq
    #
    @5
    cB
    c1o
    eldif
    @1
    @18
    @20
    @21
    @1
    @18
    wa
    @5
    con0
    wcel
    #
    @20
    @21
    wi
    @1
    cB
    word
    #
    @18
    @22
    cB
    limord
    #
    cB
    @5
    ordelon
    sylan
    @22
    @20
    c0
    @5
    wcel
    #
    @21
    @22
    @25
    @5
    c0
    wne
    @20
    @5
    on0eln0
    @19
    @5
    c0
    @5
    el1o
    necon3bbii
    syl6bbr
    @22
    @25
    @21
    @5
    oe0m1
    biimpd
    sylbird
    syl
    impr
    sylan2b
    iuneq2dv
    @1
    c1o
    @4
    wcel
    #
    @4
    c0
    wne
    @17
    c0
    wceq
    @1
    c1o
    cB
    wcel
    #
    c1o
    c1o
    wcel
    wn
    #
    wa
    @26
    @1
    @27
    @28
    @1
    c1o
    c0
    csuc
    #
    cB
    df-1o
    @1
    @14
    @29
    cB
    wcel
    @16
    cB
    c0
    limsuc
    mpbid
    syl5eqel
    c1o
    1on
    onirri
    jctir
    c1o
    cB
    c1o
    eldif
    sylibr
    @4
    c1o
    ne0i
    vx
    @4
    c0
    iunconst
    3syl
    eqtrd
    adantl
    eqtr4d
    @9
    @3
    @10
    @7
    @12
    cA
    c0
    cB
    coe
    oveq1
    @9
    vx
    @4
    @6
    @11
    cA
    c0
    @5
    coe
    oveq1
    iuneq2d
    eqeq12d
    syl5ibr
    impcom
    cA
    con0
    wcel
    #
    @2
    wa
    c0
    cA
    wcel
    #
    wa
    @3
    vy
    cB
    cA
    vy
    cv
    #
    coe
    co
    #
    ciun
    #
    @7
    vy
    cA
    cB
    cC
    oelim
    @30
    @1
    @31
    @34
    @7
    wceq
    @0
    @30
    @1
    wa
    #
    @31
    wa
    #
    @34
    @7
    @36
    @33
    @6
    wss
    #
    vx
    @4
    wrex
    #
    vy
    cB
    wral
    @34
    @7
    wss
    @36
    @38
    vy
    cB
    @36
    @32
    cB
    wcel
    #
    @32
    csuc
    #
    @4
    wcel
    #
    @33
    cA
    @40
    coe
    co
    #
    wss
    #
    wa
    @38
    @36
    @39
    @41
    @43
    @1
    @39
    @41
    wi
    @30
    @31
    @1
    @39
    @41
    @1
    @39
    wa
    #
    @40
    cB
    wcel
    #
    @40
    c0
    wne
    #
    @41
    @1
    @39
    @45
    cB
    @32
    limsuc
    biimpa
    @46
    @44
    @32
    nsuceq0
    a1i
    @40
    cB
    dif1o
    sylanbrc
    ex
    ad2antlr
    @36
    @39
    @43
    @36
    @39
    wa
    @32
    @40
    wss
    #
    @43
    @32
    sssucid
    @35
    @39
    @31
    @47
    @43
    wi
    #
    @35
    @39
    wa
    @32
    con0
    wcel
    #
    @40
    con0
    wcel
    #
    @30
    w3a
    #
    @31
    @48
    @30
    @1
    @39
    @51
    @44
    @30
    @49
    @50
    wa
    #
    @51
    @44
    @49
    @50
    @1
    @23
    @39
    @49
    @24
    cB
    @32
    ordelon
    sylan
    @32
    suceloni
    jccir
    @52
    @30
    @51
    @49
    @50
    @30
    @51
    @51
    id
    3expa
    ancoms
    sylan2
    anassrs
    @32
    @40
    cA
    oewordi
    sylan
    an32s
    mpi
    ex
    jcad
    @37
    @43
    vx
    @40
    @4
    @5
    @40
    wceq
    @6
    @42
    @33
    @5
    @40
    cA
    coe
    oveq2
    sseq2d
    rspcev
    syl6
    ralrimiv
    vy
    vx
    cB
    @4
    @33
    @6
    iunss2
    syl
    @7
    @34
    wss
    @36
    @7
    vx
    cB
    @6
    ciun
    #
    @34
    @4
    cB
    wss
    @7
    @53
    wss
    cB
    c1o
    difss
    vx
    @4
    cB
    @6
    iunss1
    ax-mp
    vx
    vy
    cB
    @6
    @33
    @5
    @32
    cA
    coe
    oveq2
    cbviunv
    sseqtri
    a1i
    eqssd
    adantlrl
    eqtrd
    oe0lem
end
