include "cnp.mm"
include "wcel.mm"
include "wpss.mm"
include "cpp.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cplq.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "ltexprlem5.mm"
include "df-plp.mm"
include "addclnq.mm"
include "genpelv.mm"
include "sylan2.mm"
include "wi.mm"
include "wn.mm"
include "wex.mm"
include "abeq2i.mm"
include "cltq.mm"
include "wbr.mm"
include "cnq.mm"
include "elprnq.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "simpld.mm"
include "syl.mm"
include "prub.mm"
include "simprd.mm"
include "vex.mm"
include "ltanq.mm"
include "addcomnq.mm"
include "caovord2.mm"
include "3syl.mm"
include "prcdnq.mm"
include "sylbid.mm"
include "adantl.mm"
include "syld.mm"
include "exp32.mm"
include "com34.mm"
include "imp4b.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "exp31.mm"
include "com23.mm"
include "imp43.mm"
include "eleq1.mm"
include "biimparc.mm"
include "sylan.mm"
include "rexlimdvv.mm"
include "adantrr.mm"
include "ssrdv.mm"
include "anassrs.mm"

theorem ltexprlem6
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  assume ltexprlem.1: |- C = { x | E. y ( -. y e. A /\ ( y +Q x ) e. B ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint w z
  disjoint v z
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint A z
  disjoint v w
  disjoint f w
  disjoint g w
  disjoint h w
  disjoint A w
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint A v
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint C z
  disjoint C w
  disjoint C v
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint u w
  disjoint u v
  disjoint f u
  disjoint g u
  disjoint h u
  assert |- ( ( ( A e. P. /\ B e. P. ) /\ A C. B ) -> ( A +P. C ) C_ B )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    cA
    cB
    wpss
    #
    cA
    cC
    cpp
    co
    #
    cB
    wss
    @0
    @1
    @2
    wa
    #
    wa
    #
    vz
    @3
    cB
    @5
    vz
    cv
    #
    @3
    wcel
    #
    @6
    vw
    cv
    #
    vx
    cv
    #
    cplq
    co
    #
    wceq
    #
    vx
    cC
    wrex
    vw
    cA
    wrex
    #
    @6
    cB
    wcel
    #
    @4
    @0
    cC
    cnp
    wcel
    @7
    @12
    wb
    vx
    vy
    cA
    cB
    cC
    ltexprlem.1
    ltexprlem5
    vf
    vg
    vh
    vz
    vy
    cA
    cC
    @6
    vw
    vx
    cpp
    cplq
    vz
    vy
    vf
    vg
    vh
    df-plp
    vg
    cv
    vh
    cv
    addclnq
    genpelv
    sylan2
    @0
    @1
    @12
    @13
    wi
    @2
    @0
    @1
    wa
    #
    @11
    @13
    vw
    vx
    cA
    cC
    @14
    @8
    cA
    wcel
    #
    @9
    cC
    wcel
    #
    wa
    #
    @11
    @13
    @14
    @17
    wa
    @10
    cB
    wcel
    #
    @11
    @13
    @0
    @1
    @15
    @16
    @18
    @0
    @15
    @1
    @16
    @18
    wi
    #
    @0
    @15
    @1
    @19
    @16
    vy
    cv
    #
    cA
    wcel
    wn
    #
    @20
    @9
    cplq
    co
    #
    cB
    wcel
    #
    wa
    #
    vy
    wex
    #
    @0
    @15
    wa
    #
    @1
    wa
    #
    @18
    @25
    vx
    cC
    ltexprlem.1
    abeq2i
    @27
    @24
    @18
    vy
    @26
    @1
    @21
    @23
    @18
    @26
    @1
    @23
    @21
    @18
    @26
    @1
    @23
    @21
    @18
    wi
    @26
    @1
    @23
    wa
    #
    wa
    @21
    @8
    @20
    cltq
    wbr
    #
    @18
    @28
    @26
    @20
    cnq
    wcel
    #
    @21
    @29
    wi
    @28
    @22
    cnq
    wcel
    #
    @30
    cB
    @22
    elprnq
    #
    @31
    @30
    @9
    cnq
    wcel
    #
    @20
    @9
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
    fdmi
    0nnq
    ndmovrcl
    #
    simpld
    syl
    cA
    @8
    @20
    prub
    sylan2
    @28
    @29
    @18
    wi
    @26
    @28
    @29
    @10
    @22
    cltq
    wbr
    #
    @18
    @28
    @31
    @33
    @29
    @35
    wb
    @32
    @31
    @30
    @33
    @34
    simprd
    vz
    vv
    vu
    @8
    @20
    @9
    cltq
    cnq
    cplq
    vw
    vex
    vy
    vex
    @6
    vv
    cv
    #
    vu
    cv
    ltanq
    vx
    vex
    @6
    @36
    addcomnq
    caovord2
    3syl
    cB
    @22
    @10
    prcdnq
    sylbid
    adantl
    syld
    exp32
    com34
    imp4b
    exlimdv
    syl5bi
    exp31
    com23
    imp43
    @11
    @13
    @18
    @6
    @10
    cB
    eleq1
    biimparc
    sylan
    exp31
    rexlimdvv
    adantrr
    sylbid
    ssrdv
    anassrs
end
