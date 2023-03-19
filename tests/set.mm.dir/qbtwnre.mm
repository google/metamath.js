include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "cq.mm"
include "wrex.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cn.mm"
include "cc0.mm"
include "posdif.mm"
include "wi.mm"
include "resubcl.mm"
include "nnrecl.mm"
include "sylan.mm"
include "ex.mm"
include "ancoms.mm"
include "sylbid.mm"
include "cmul.mm"
include "cle.mm"
include "caddc.mm"
include "cz.mm"
include "wreu.mm"
include "nnre.mm"
include "adantl.mm"
include "simplr.mm"
include "remulcld.mm"
include "peano2rem.mm"
include "syl.mm"
include "zbtwnre.mm"
include "reurex.mm"
include "3syl.mm"
include "znq.mm"
include "an32.mm"
include "ad2antrl.mm"
include "simpll.mm"
include "adantrr.mm"
include "zre.mm"
include "ad2antll.mm"
include "ltletr.mm"
include "syl3anc.mm"
include "recnd.mm"
include "subdid.mm"
include "breq2d.mm"
include "wb.mm"
include "1red.mm"
include "resubcld.mm"
include "nngt0.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "ltsub13.mm"
include "3bitr4rd.mm"
include "anbi1d.mm"
include "ancom.mm"
include "syl6bb.mm"
include "ltmuldiv2.mm"
include "3imtr3d.mm"
include "cc.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "sylancl.mm"
include "bitr4d.mm"
include "biimpd.mm"
include "anim12d.mm"
include "syl5bi.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl6an.mm"
include "expd.mm"
include "expr.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "rexlimdva.mm"
include "syld.mm"
include "3impia.mm"

theorem qbtwnre
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B y
  disjoint B z
  assert |- ( ( A e. RR /\ B e. RR /\ A < B ) -> E. x e. QQ ( A < x /\ x < B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    cA
    vx
    cv
    #
    clt
    wbr
    #
    @3
    cB
    clt
    wbr
    #
    wa
    #
    vx
    cq
    wrex
    #
    @0
    @1
    wa
    #
    @2
    c1
    vy
    cv
    #
    cdiv
    co
    cB
    cA
    cmin
    co
    #
    clt
    wbr
    #
    vy
    cn
    wrex
    #
    @7
    @8
    @2
    cc0
    @10
    clt
    wbr
    #
    @12
    cA
    cB
    posdif
    @1
    @0
    @13
    @12
    wi
    @1
    @0
    wa
    #
    @13
    @12
    @14
    @10
    cr
    wcel
    #
    @13
    @12
    cB
    cA
    resubcl
    @10
    vy
    nnrecl
    sylan
    ex
    ancoms
    sylbid
    @8
    @11
    @7
    vy
    cn
    @8
    @9
    cn
    wcel
    #
    wa
    #
    @9
    cB
    cmul
    co
    #
    c1
    cmin
    co
    #
    vz
    cv
    #
    cle
    wbr
    #
    @20
    @19
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vz
    cz
    wrex
    #
    @11
    @7
    wi
    #
    @17
    @19
    cr
    wcel
    #
    @24
    vz
    cz
    wreu
    @25
    @17
    @18
    cr
    wcel
    #
    @27
    @17
    @9
    cB
    @16
    @9
    cr
    wcel
    #
    @8
    @9
    nnre
    #
    adantl
    @0
    @1
    @16
    simplr
    remulcld
    #
    @18
    peano2rem
    syl
    #
    vz
    @19
    zbtwnre
    @24
    vz
    cz
    reurex
    3syl
    @17
    @24
    @26
    vz
    cz
    @8
    @16
    @20
    cz
    wcel
    #
    @24
    @26
    wi
    @8
    @16
    @33
    wa
    #
    wa
    #
    @24
    @11
    @7
    @35
    @20
    @9
    cdiv
    co
    #
    cq
    wcel
    #
    @24
    @11
    wa
    #
    cA
    @36
    clt
    wbr
    #
    @36
    cB
    clt
    wbr
    #
    wa
    #
    @7
    @34
    @37
    @8
    @33
    @16
    @37
    @20
    @9
    znq
    ancoms
    adantl
    @38
    @21
    @11
    wa
    #
    @23
    wa
    @35
    @41
    @21
    @23
    @11
    an32
    @35
    @42
    @39
    @23
    @40
    @35
    @9
    cA
    cmul
    co
    #
    @19
    clt
    wbr
    #
    @21
    wa
    #
    @43
    @20
    clt
    wbr
    #
    @42
    @39
    @35
    @43
    cr
    wcel
    #
    @27
    @20
    cr
    wcel
    #
    @45
    @46
    wi
    @35
    @9
    cA
    @16
    @29
    @8
    @33
    @30
    ad2antrl
    #
    @0
    @1
    @34
    simpll
    #
    remulcld
    #
    @8
    @16
    @27
    @33
    @32
    adantrr
    @33
    @48
    @8
    @16
    @20
    zre
    ad2antll
    #
    @43
    @19
    @20
    ltletr
    syl3anc
    @35
    @45
    @11
    @21
    wa
    @42
    @35
    @44
    @11
    @21
    @35
    c1
    @9
    @10
    cmul
    co
    #
    clt
    wbr
    #
    c1
    @18
    @43
    cmin
    co
    #
    clt
    wbr
    #
    @11
    @44
    @35
    @53
    @55
    c1
    clt
    @35
    @9
    cB
    cA
    @35
    @9
    @49
    recnd
    @35
    cB
    @0
    @1
    @34
    simplr
    #
    recnd
    @35
    cA
    @50
    recnd
    subdid
    breq2d
    @35
    c1
    cr
    wcel
    #
    @15
    @29
    cc0
    @9
    clt
    wbr
    #
    @11
    @54
    wb
    @35
    1red
    #
    @35
    cB
    cA
    @57
    @50
    resubcld
    @49
    @16
    @59
    @8
    @33
    @9
    nngt0
    ad2antrl
    #
    c1
    @10
    @9
    ltdivmul
    syl112anc
    @35
    @47
    @28
    @58
    @44
    @56
    wb
    @51
    @8
    @16
    @28
    @33
    @31
    adantrr
    #
    @60
    @43
    @18
    c1
    ltsub13
    syl3anc
    3bitr4rd
    anbi1d
    @11
    @21
    ancom
    syl6bb
    @35
    @0
    @48
    @29
    @59
    @46
    @39
    wb
    @50
    @52
    @49
    @61
    cA
    @20
    @9
    ltmuldiv2
    syl112anc
    3imtr3d
    @35
    @23
    @40
    @35
    @23
    @20
    @18
    clt
    wbr
    #
    @40
    @35
    @22
    @18
    @20
    clt
    @35
    @18
    cc
    wcel
    c1
    cc
    wcel
    @22
    @18
    wceq
    @35
    @18
    @62
    recnd
    ax-1cn
    @18
    c1
    npcan
    sylancl
    breq2d
    @35
    @48
    @1
    @29
    @59
    @40
    @63
    wb
    @52
    @57
    @49
    @61
    @20
    cB
    @9
    ltdivmul
    syl112anc
    bitr4d
    biimpd
    anim12d
    syl5bi
    @6
    @41
    vx
    @36
    cq
    @3
    @36
    wceq
    @4
    @39
    @5
    @40
    @3
    @36
    cA
    clt
    breq2
    @3
    @36
    cB
    clt
    breq1
    anbi12d
    rspcev
    syl6an
    expd
    expr
    rexlimdv
    mpd
    rexlimdva
    syld
    3impia
end
