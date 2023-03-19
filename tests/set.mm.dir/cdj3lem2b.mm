include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cno.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cva.mm"
include "cmul.mm"
include "cle.mm"
include "wral.mm"
include "wa.mm"
include "cr.mm"
include "wrex.mm"
include "cph.mm"
include "cdj3lem1.mm"
include "wcel.mm"
include "wi.mm"
include "shseli.mm"
include "biimpi.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "cdj3lem2.mm"
include "3expa.mm"
include "ad2ant2r.mm"
include "chil.mm"
include "sheli.mm"
include "normge0.mm"
include "syl.mm"
include "adantl.mm"
include "wb.mm"
include "normcl.mm"
include "addge01.mm"
include "syl2an.mm"
include "mpbid.mm"
include "adantr.mm"
include "ad2antrr.mm"
include "readdcl.mm"
include "hvaddcl.mm"
include "remulcl.mm"
include "sylan2.mm"
include "ancoms.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "imp.mm"
include "an32s.mm"
include "adantrl.mm"
include "eqbrtrd.mm"
include "syl5ibrcom.mm"
include "exp31.mm"
include "syld.mm"
include "com14.mm"
include "com4t.mm"
include "rexlimdvv.mm"
include "syl5com.mm"
include "com3l.mm"
include "ralrimdv.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpcom.mm"

theorem cdj3lem2b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  let vt: setvar t
  let vh: setvar h
  let cC: class C
  let cD: class D
  assume cdj3lem2.1: |- A e. SH
  assume cdj3lem2.2: |- B e. SH
  assume cdj3lem2.3: |- S = ( x e. ( A +H B ) |-> ( iota_ z e. A E. w e. B x = ( z +h w ) ) )

  disjoint u v
  disjoint S v
  disjoint S u
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint A y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint A w
  disjoint u v
  disjoint A v
  disjoint A u
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint t v
  disjoint h v
  disjoint t u
  disjoint h u
  disjoint h t
  disjoint S t
  disjoint S h
  disjoint t x
  disjoint h x
  disjoint t y
  disjoint h y
  disjoint t z
  disjoint h z
  disjoint t w
  disjoint h w
  disjoint t v
  disjoint h v
  disjoint t u
  disjoint h u
  disjoint h t
  disjoint A t
  disjoint A h
  disjoint B t
  disjoint B h
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint C w
  disjoint C v
  disjoint C u
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint D w
  assert |- ( E. v e. RR ( 0 < v /\ A. x e. A A. y e. B ( ( normh ` x ) + ( normh ` y ) ) <_ ( v x. ( normh ` ( x +h y ) ) ) ) -> E. v e. RR ( 0 < v /\ A. u e. ( A +H B ) ( normh ` ( S ` u ) ) <_ ( v x. ( normh ` u ) ) ) )

  proof
    cA
    cB
    cin
    c0h
    wceq
    #
    cc0
    vv
    cv
    #
    clt
    wbr
    #
    vx
    cv
    #
    cno
    cfv
    #
    vy
    cv
    #
    cno
    cfv
    #
    caddc
    co
    #
    @1
    @3
    @5
    cva
    co
    #
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    cB
    wral
    vx
    cA
    wral
    #
    wa
    #
    vv
    cr
    wrex
    @2
    vu
    cv
    #
    cS
    cfv
    #
    cno
    cfv
    #
    @1
    @14
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vu
    cA
    cB
    cph
    co
    #
    wral
    #
    wa
    #
    vv
    cr
    wrex
    vv
    vx
    vy
    cA
    cB
    cdj3lem2.1
    cdj3lem2.2
    cdj3lem1
    @0
    @13
    @22
    vv
    cr
    @0
    @1
    cr
    wcel
    #
    wa
    #
    @12
    @21
    @2
    @24
    @12
    @19
    vu
    @20
    @14
    @20
    wcel
    #
    @24
    @12
    @19
    @25
    @14
    vt
    cv
    #
    vh
    cv
    #
    cva
    co
    #
    wceq
    #
    vh
    cB
    wrex
    vt
    cA
    wrex
    #
    @24
    @12
    @19
    wi
    #
    @25
    @30
    vt
    vh
    cA
    cB
    @14
    cdj3lem2.1
    cdj3lem2.2
    shseli
    biimpi
    @24
    @29
    @31
    vt
    vh
    cA
    cB
    @29
    @12
    @24
    @26
    cA
    wcel
    #
    @27
    cB
    wcel
    #
    wa
    #
    @19
    @34
    @12
    @24
    @29
    @19
    @34
    @12
    @26
    cno
    cfv
    #
    @27
    cno
    cfv
    #
    caddc
    co
    #
    @1
    @28
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    @24
    @29
    @19
    wi
    #
    wi
    @11
    @40
    @35
    @6
    caddc
    co
    #
    @1
    @26
    @5
    cva
    co
    #
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    vx
    vy
    @26
    @27
    cA
    cB
    @3
    @26
    wceq
    #
    @7
    @42
    @10
    @45
    cle
    @46
    @4
    @35
    @6
    caddc
    @3
    @26
    cno
    fveq2
    oveq1d
    @46
    @9
    @44
    @1
    cmul
    @46
    @8
    @43
    cno
    @3
    @26
    @5
    cva
    oveq1
    fveq2d
    oveq2d
    breq12d
    @5
    @27
    wceq
    #
    @42
    @37
    @45
    @39
    cle
    @47
    @6
    @36
    @35
    caddc
    @5
    @27
    cno
    fveq2
    oveq2d
    @47
    @44
    @38
    @1
    cmul
    @47
    @43
    @28
    cno
    @5
    @27
    @26
    cva
    oveq2
    fveq2d
    oveq2d
    breq12d
    rspc2v
    @34
    @40
    @24
    @41
    @34
    @40
    wa
    #
    @24
    wa
    #
    @19
    @29
    @28
    cS
    cfv
    #
    cno
    cfv
    #
    @39
    cle
    wbr
    @49
    @51
    @35
    @39
    cle
    @34
    @0
    @51
    @35
    wceq
    @40
    @23
    @34
    @0
    wa
    @50
    @26
    cno
    @32
    @33
    @0
    @50
    @26
    wceq
    vx
    vz
    vw
    cA
    cB
    @26
    @27
    cS
    cdj3lem2.1
    cdj3lem2.2
    cdj3lem2.3
    cdj3lem2
    3expa
    fveq2d
    ad2ant2r
    @48
    @23
    @35
    @39
    cle
    wbr
    #
    @0
    @34
    @23
    @40
    @52
    @34
    @23
    wa
    #
    @40
    @52
    @53
    @35
    @37
    cle
    wbr
    #
    @40
    @52
    @34
    @54
    @23
    @34
    cc0
    @36
    cle
    wbr
    #
    @54
    @33
    @55
    @32
    @33
    @27
    chil
    wcel
    #
    @55
    @27
    cB
    cdj3lem2.2
    sheli
    #
    @27
    normge0
    syl
    adantl
    @32
    @35
    cr
    wcel
    #
    @36
    cr
    wcel
    #
    @55
    @54
    wb
    @33
    @32
    @26
    chil
    wcel
    #
    @58
    @26
    cA
    cdj3lem2.1
    sheli
    #
    @26
    normcl
    syl
    #
    @33
    @56
    @59
    @57
    @27
    normcl
    syl
    #
    @35
    @36
    addge01
    syl2an
    mpbid
    adantr
    @53
    @58
    @37
    cr
    wcel
    #
    @39
    cr
    wcel
    #
    @54
    @40
    wa
    @52
    wi
    @32
    @58
    @33
    @23
    @62
    ad2antrr
    @34
    @64
    @23
    @32
    @58
    @59
    @64
    @33
    @62
    @63
    @35
    @36
    readdcl
    syl2an
    adantr
    @23
    @34
    @65
    @34
    @23
    @38
    cr
    wcel
    #
    @65
    @34
    @28
    chil
    wcel
    #
    @66
    @32
    @60
    @56
    @67
    @33
    @61
    @57
    @26
    @27
    hvaddcl
    syl2an
    @28
    normcl
    syl
    @1
    @38
    remulcl
    sylan2
    ancoms
    @35
    @37
    @39
    letr
    syl3anc
    mpand
    imp
    an32s
    adantrl
    eqbrtrd
    @29
    @16
    @51
    @18
    @39
    cle
    @29
    @15
    @50
    cno
    @14
    @28
    cS
    fveq2
    fveq2d
    @29
    @17
    @38
    @1
    cmul
    @14
    @28
    cno
    fveq2
    oveq2d
    breq12d
    syl5ibrcom
    exp31
    syld
    com14
    com4t
    rexlimdvv
    syl5com
    com3l
    ralrimdv
    anim2d
    reximdva
    mpcom
end
