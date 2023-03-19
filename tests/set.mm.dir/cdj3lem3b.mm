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
include "wceq.mm"
include "crio.mm"
include "cmpt.mm"
include "shscomi.mm"
include "wcel.mm"
include "chil.mm"
include "sheli.mm"
include "ax-hvcom.mm"
include "syl2an.mm"
include "eqeq2d.mm"
include "rexbidva.mm"
include "riotabiia.mm"
include "mpteq12i.mm"
include "eqtr4i.mm"
include "cdj3lem2b.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "breq12d.mm"
include "oveq2.mm"
include "cbvral2v.mm"
include "ralcom.mm"
include "cc.mm"
include "normcl.mm"
include "syl.mm"
include "recnd.mm"
include "addcom.mm"
include "ralbidva.mm"
include "ralbiia.mm"
include "bitr2i.mm"
include "3bitri.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "raleqi.mm"
include "3imtr4i.mm"

theorem cdj3lem3b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cT: class T
  let vt: setvar t
  let vh: setvar h
  let cC: class C
  let cD: class D
  assume cdj3lem2.1: |- A e. SH
  assume cdj3lem2.2: |- B e. SH
  assume cdj3lem3.3: |- T = ( x e. ( A +H B ) |-> ( iota_ w e. B E. z e. A x = ( z +h w ) ) )

  disjoint u v
  disjoint T v
  disjoint T u
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
  disjoint T t
  disjoint T h
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
  assert |- ( E. v e. RR ( 0 < v /\ A. x e. A A. y e. B ( ( normh ` x ) + ( normh ` y ) ) <_ ( v x. ( normh ` ( x +h y ) ) ) ) -> E. v e. RR ( 0 < v /\ A. u e. ( A +H B ) ( normh ` ( T ` u ) ) <_ ( v x. ( normh ` u ) ) ) )

  proof
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
    @0
    @2
    @4
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
    cA
    wral
    #
    vx
    cB
    wral
    #
    wa
    #
    vv
    cr
    wrex
    @1
    vu
    cv
    #
    cT
    cfv
    cno
    cfv
    @0
    @14
    cno
    cfv
    cmul
    co
    cle
    wbr
    #
    vu
    cB
    cA
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
    @1
    @10
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
    @1
    @15
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
    vx
    vy
    vw
    vz
    vv
    vu
    cB
    cA
    cT
    cdj3lem2.2
    cdj3lem2.1
    cT
    vx
    @21
    @2
    vz
    cv
    #
    vw
    cv
    #
    cva
    co
    #
    wceq
    #
    vz
    cA
    wrex
    #
    vw
    cB
    crio
    #
    cmpt
    vx
    @16
    @2
    @25
    @24
    cva
    co
    #
    wceq
    #
    vz
    cA
    wrex
    #
    vw
    cB
    crio
    #
    cmpt
    cdj3lem3.3
    vx
    @16
    @33
    @21
    @29
    cB
    cA
    cdj3lem2.2
    cdj3lem2.1
    shscomi
    @32
    @28
    vw
    cB
    @25
    cB
    wcel
    #
    @31
    @27
    vz
    cA
    @34
    @24
    cA
    wcel
    #
    wa
    @30
    @26
    @2
    @34
    @25
    chil
    wcel
    @24
    chil
    wcel
    @30
    @26
    wceq
    @35
    @25
    cB
    cdj3lem2.2
    sheli
    @24
    cA
    cdj3lem2.1
    sheli
    @25
    @24
    ax-hvcom
    syl2an
    eqeq2d
    rexbidva
    riotabiia
    mpteq12i
    eqtr4i
    cdj3lem2b
    @20
    @13
    vv
    cr
    @19
    @12
    @1
    @19
    vt
    cv
    #
    cno
    cfv
    #
    vh
    cv
    #
    cno
    cfv
    #
    caddc
    co
    #
    @0
    @36
    @38
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
    vh
    cB
    wral
    vt
    cA
    wral
    @44
    vt
    cA
    wral
    vh
    cB
    wral
    #
    @12
    @10
    @44
    @37
    @5
    caddc
    co
    #
    @0
    @36
    @4
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
    vt
    vh
    cA
    cB
    @2
    @36
    wceq
    #
    @6
    @46
    @9
    @49
    cle
    @50
    @3
    @37
    @5
    caddc
    @2
    @36
    cno
    fveq2
    oveq1d
    @50
    @8
    @48
    @0
    cmul
    @50
    @7
    @47
    cno
    @2
    @36
    @4
    cva
    oveq1
    fveq2d
    oveq2d
    breq12d
    @4
    @38
    wceq
    #
    @46
    @40
    @49
    @43
    cle
    @51
    @5
    @39
    @37
    caddc
    @4
    @38
    cno
    fveq2
    oveq2d
    @51
    @48
    @42
    @0
    cmul
    @51
    @47
    @41
    cno
    @4
    @38
    @36
    cva
    oveq2
    fveq2d
    oveq2d
    breq12d
    cbvral2v
    @44
    vt
    vh
    cA
    cB
    ralcom
    @12
    @5
    @3
    caddc
    co
    #
    @0
    @4
    @2
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
    cA
    wral
    #
    vx
    cB
    wral
    @45
    @11
    @57
    vx
    cB
    @2
    cB
    wcel
    #
    @10
    @56
    vy
    cA
    @58
    @4
    cA
    wcel
    #
    wa
    #
    @6
    @52
    @9
    @55
    cle
    @58
    @3
    cc
    wcel
    @5
    cc
    wcel
    @6
    @52
    wceq
    @59
    @58
    @3
    @58
    @2
    chil
    wcel
    #
    @3
    cr
    wcel
    @2
    cB
    cdj3lem2.2
    sheli
    #
    @2
    normcl
    syl
    recnd
    @59
    @5
    @59
    @4
    chil
    wcel
    #
    @5
    cr
    wcel
    @4
    cA
    cdj3lem2.1
    sheli
    #
    @4
    normcl
    syl
    recnd
    @3
    @5
    addcom
    syl2an
    @60
    @8
    @54
    @0
    cmul
    @60
    @7
    @53
    cno
    @58
    @61
    @63
    @7
    @53
    wceq
    @59
    @62
    @64
    @2
    @4
    ax-hvcom
    syl2an
    fveq2d
    oveq2d
    breq12d
    ralbidva
    ralbiia
    @56
    @44
    @5
    @39
    caddc
    co
    #
    @0
    @4
    @38
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
    vh
    vt
    cB
    cA
    @2
    @38
    wceq
    #
    @52
    @65
    @55
    @68
    cle
    @69
    @3
    @39
    @5
    caddc
    @2
    @38
    cno
    fveq2
    oveq2d
    @69
    @54
    @67
    @0
    cmul
    @69
    @53
    @66
    cno
    @2
    @38
    @4
    cva
    oveq2
    fveq2d
    oveq2d
    breq12d
    @4
    @36
    wceq
    #
    @65
    @40
    @68
    @43
    cle
    @70
    @5
    @37
    @39
    caddc
    @4
    @36
    cno
    fveq2
    oveq1d
    @70
    @67
    @42
    @0
    cmul
    @70
    @66
    @41
    cno
    @4
    @36
    @38
    cva
    oveq1
    fveq2d
    oveq2d
    breq12d
    cbvral2v
    bitr2i
    3bitri
    anbi2i
    rexbii
    @23
    @18
    vv
    cr
    @22
    @17
    @1
    @15
    vu
    @21
    @16
    cA
    cB
    cdj3lem2.1
    cdj3lem2.2
    shscomi
    raleqi
    anbi2i
    rexbii
    3imtr4i
end
