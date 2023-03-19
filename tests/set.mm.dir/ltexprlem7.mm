include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "wpss.mm"
include "cpp.mm"
include "co.mm"
include "cv.mm"
include "wi.mm"
include "ltexprlem5.mm"
include "cltp.mm"
include "wbr.mm"
include "ltaddpr.mm"
include "wb.mm"
include "addclpr.mm"
include "ltprord.mm"
include "syldan.mm"
include "mpbid.mm"
include "pssssd.mm"
include "sseld.mm"
include "2a1d.mm"
include "com4r.mm"
include "expd.mm"
include "wn.mm"
include "cplq.mm"
include "wex.mm"
include "prnmadd.mm"
include "ex.mm"
include "cnq.mm"
include "elprnq.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "syl.mm"
include "simpld.mm"
include "wrex.mm"
include "vex.mm"
include "prlem934.mm"
include "adantr.mm"
include "wceq.mm"
include "cltq.mm"
include "prub.mm"
include "ltexnq.mm"
include "adantl.mm"
include "sylibd.mm"
include "ad2ant2r.mm"
include "addcomnq.mm"
include "addassnq.mm"
include "caov32.mm"
include "oveq1.mm"
include "syl5eq.mm"
include "eleq1d.mm"
include "biimpar.mm"
include "ovex.mm"
include "eleq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "spcev.mm"
include "abeq2i.mm"
include "sylibr.mm"
include "sylan2.mm"
include "df-plp.mm"
include "addclnq.mm"
include "genpprecl.mm"
include "sylan2i.mm"
include "exp4d.mm"
include "imp42.mm"
include "ad2antrl.mm"
include "exp32.mm"
include "exlimdv.mm"
include "syl6d.mm"
include "rexlimddv.mm"
include "com14.mm"
include "mpd.mm"
include "syld.mm"
include "com4t.mm"
include "pm2.61i.mm"
include "syl5.mm"
include "com34.mm"
include "pm2.43d.mm"
include "imp31.mm"
include "ssrdv.mm"

theorem ltexprlem7
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
  assert |- ( ( ( A e. P. /\ B e. P. ) /\ A C. B ) -> B C_ ( A +P. C ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    cA
    cB
    wpss
    #
    wa
    vw
    cB
    cA
    cC
    cpp
    co
    #
    @0
    @1
    @2
    vw
    cv
    #
    cB
    wcel
    #
    @4
    @3
    wcel
    #
    wi
    #
    @0
    @1
    @2
    @7
    wi
    @0
    @1
    @2
    @1
    @7
    @0
    @1
    @2
    @1
    @7
    wi
    #
    @1
    @2
    wa
    cC
    cnp
    wcel
    #
    @0
    @8
    vx
    vy
    cA
    cB
    cC
    ltexprlem.1
    ltexprlem5
    @4
    cA
    wcel
    #
    @0
    @9
    @8
    wi
    wi
    @10
    @0
    @9
    @8
    @0
    @9
    wa
    #
    @1
    @5
    @10
    @6
    @11
    @10
    @6
    wi
    @1
    @5
    @11
    cA
    @3
    @4
    @11
    cA
    @3
    @11
    cA
    @3
    cltp
    wbr
    #
    cA
    @3
    wpss
    #
    cA
    cC
    ltaddpr
    @0
    @9
    @3
    cnp
    wcel
    @12
    @13
    wb
    cA
    cC
    addclpr
    cA
    @3
    ltprord
    syldan
    mpbid
    pssssd
    sseld
    2a1d
    com4r
    expd
    @10
    wn
    #
    @0
    @9
    @8
    @1
    @5
    @14
    @11
    @6
    @1
    @5
    @4
    vv
    cv
    #
    cplq
    co
    #
    cB
    wcel
    #
    vv
    wex
    #
    @14
    @11
    @6
    wi
    wi
    #
    @1
    @5
    @18
    vv
    cB
    @4
    prnmadd
    ex
    @1
    @17
    @19
    vv
    @1
    @17
    @19
    @1
    @17
    wa
    #
    @4
    cnq
    wcel
    #
    @19
    @20
    @21
    @15
    cnq
    wcel
    #
    @20
    @16
    cnq
    wcel
    @21
    @22
    wa
    cB
    @16
    elprnq
    @4
    @15
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
    syl
    simpld
    @17
    @21
    @19
    wi
    @1
    @11
    @21
    @14
    @17
    @6
    @11
    vz
    cv
    #
    @15
    cplq
    co
    #
    cA
    wcel
    #
    wn
    #
    @21
    @14
    @17
    @6
    wi
    #
    wi
    wi
    vz
    cA
    @0
    @26
    vz
    cA
    wrex
    @9
    vz
    cA
    @15
    vv
    vex
    #
    prlem934
    adantr
    @11
    @23
    cA
    wcel
    #
    @26
    wa
    wa
    #
    @21
    @14
    @23
    vx
    cv
    #
    cplq
    co
    #
    @4
    wceq
    #
    vx
    wex
    #
    @27
    @0
    @29
    @21
    @14
    @34
    wi
    #
    wi
    @9
    @26
    @0
    @29
    wa
    #
    @21
    @35
    @36
    @21
    wa
    @14
    @23
    @4
    cltq
    wbr
    #
    @34
    cA
    @23
    @4
    prub
    @21
    @37
    @34
    wb
    @36
    vx
    @23
    @4
    ltexnq
    adantl
    sylibd
    ex
    ad2ant2r
    @30
    @33
    @27
    vx
    @30
    @33
    @17
    @6
    @30
    @33
    @17
    wa
    #
    wa
    @32
    @3
    wcel
    #
    @6
    @11
    @29
    @26
    @38
    @39
    @11
    @29
    @26
    @38
    @39
    @26
    @38
    wa
    @11
    @29
    @31
    cC
    wcel
    #
    @39
    @38
    @26
    @24
    @31
    cplq
    co
    #
    cB
    wcel
    #
    @40
    @33
    @42
    @17
    @33
    @41
    @16
    cB
    @33
    @41
    @32
    @15
    cplq
    co
    @16
    vf
    vg
    vh
    @23
    @15
    @31
    cplq
    vz
    vex
    @28
    vx
    vex
    vf
    cv
    #
    vg
    cv
    #
    addcomnq
    @43
    @44
    vh
    cv
    addassnq
    caov32
    @32
    @4
    @15
    cplq
    oveq1
    syl5eq
    eleq1d
    biimpar
    @26
    @42
    wa
    #
    vy
    cv
    #
    cA
    wcel
    #
    wn
    #
    @46
    @31
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
    @40
    @51
    @45
    vy
    @24
    @23
    @15
    cplq
    ovex
    @46
    @24
    wceq
    #
    @48
    @26
    @50
    @42
    @53
    @47
    @25
    @46
    @24
    cA
    eleq1
    notbid
    @53
    @49
    @41
    cB
    @46
    @24
    @31
    cplq
    oveq1
    eleq1d
    anbi12d
    spcev
    @52
    vx
    cC
    ltexprlem.1
    abeq2i
    sylibr
    sylan2
    vz
    vf
    vv
    vx
    vw
    cA
    cC
    @23
    @31
    cpp
    cplq
    vx
    vw
    vz
    vf
    vv
    df-plp
    @43
    @15
    addclnq
    genpprecl
    sylan2i
    exp4d
    imp42
    @33
    @39
    @6
    wb
    @30
    @17
    @32
    @4
    @3
    eleq1
    ad2antrl
    mpbid
    exp32
    exlimdv
    syl6d
    rexlimddv
    com14
    adantl
    mpd
    ex
    exlimdv
    syld
    com4t
    expd
    pm2.61i
    syl5
    expd
    com34
    pm2.43d
    imp31
    ssrdv
end
