include "cnp.mm"
include "wcel.mm"
include "c1p.mm"
include "cmp.mm"
include "co.mm"
include "cv.mm"
include "c1q.mm"
include "cltq.mm"
include "wbr.mm"
include "df-1p.mm"
include "abeq2i.mm"
include "wa.mm"
include "crq.mm"
include "cfv.mm"
include "cmq.mm"
include "wn.mm"
include "wrex.mm"
include "ltrnq.mm"
include "mulcomnq.mm"
include "cnq.mm"
include "wceq.mm"
include "1nq.mm"
include "recclnq.mm"
include "mulidnq.mm"
include "mp2b.mm"
include "recidnq.mm"
include "ax-mp.mm"
include "3eqtr3i.mm"
include "breq1i.mm"
include "bitri.mm"
include "prlem936.mm"
include "sylan2b.mm"
include "prnmax.mm"
include "ad2ant2r.mm"
include "w3a.mm"
include "elprnq.mm"
include "3adant3.mm"
include "simp1r.mm"
include "ltrelnq.mm"
include "brel.mm"
include "simpld.mm"
include "syl.mm"
include "simp3.mm"
include "simp2r.mm"
include "wb.mm"
include "fvex.mm"
include "ltmnq.mm"
include "vex.mm"
include "caovord2.mm"
include "syl5bb.mm"
include "adantl.mm"
include "biimpd.mm"
include "syl5eqr.mm"
include "oveqan12d.mm"
include "mulassnq.mm"
include "caov4.mm"
include "3eqtr3g.mm"
include "mulclnq.mm"
include "sylan.mm"
include "recmulnq.mm"
include "mpbird.mm"
include "eleq1d.mm"
include "notbid.mm"
include "biimprd.mm"
include "anim12d.mm"
include "wex.mm"
include "ovex.mm"
include "breq2.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "spcev.mm"
include "breq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "elab2.mm"
include "sylibr.mm"
include "syl6.mm"
include "imp.mm"
include "syl22anc.mm"
include "simprd.mm"
include "3ad2ant3.mm"
include "syl5reqr.mm"
include "oveq1d.mm"
include "sylan9eqr.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "3expia.mm"
include "reximdv.mm"
include "reclem2pr.mm"
include "df-mp.mm"
include "genpelv.mm"
include "mpdan.mm"
include "ad2antrr.mm"
include "sylibrd.mm"
include "mpd.mm"
include "rexlimddv.mm"
include "ex.mm"
include "syl5bi.mm"
include "ssrdv.mm"

theorem reclem3pr
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vf: setvar f
  let vg: setvar g
  assume reclempr.1: |- B = { x | E. y ( x <Q y /\ -. ( *Q ` y ) e. A ) }

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint x z
  disjoint w x
  disjoint v x
  disjoint u x
  disjoint f x
  disjoint g x
  disjoint y z
  disjoint w y
  disjoint v y
  disjoint u y
  disjoint f y
  disjoint g y
  disjoint w z
  disjoint v z
  disjoint u z
  disjoint f z
  disjoint g z
  disjoint A z
  disjoint v w
  disjoint u w
  disjoint f w
  disjoint g w
  disjoint A w
  disjoint u v
  disjoint f v
  disjoint g v
  disjoint A v
  disjoint f u
  disjoint g u
  disjoint A u
  disjoint f g
  disjoint A f
  disjoint A g
  disjoint B z
  disjoint B w
  disjoint B v
  disjoint B u
  disjoint B f
  disjoint B g
  assert |- ( A e. P. -> 1P C_ ( A .P. B ) )

  proof
    cA
    cnp
    wcel
    #
    vw
    c1p
    cA
    cB
    cmp
    co
    #
    vw
    cv
    #
    c1p
    wcel
    @2
    c1q
    cltq
    wbr
    #
    @0
    @2
    @1
    wcel
    #
    @3
    vw
    c1p
    vw
    df-1p
    abeq2i
    @0
    @3
    @4
    @0
    @3
    wa
    #
    vv
    cv
    #
    @2
    crq
    cfv
    #
    cmq
    co
    #
    cA
    wcel
    #
    wn
    #
    @4
    vv
    cA
    @3
    @0
    c1q
    @7
    cltq
    wbr
    #
    @10
    vv
    cA
    wrex
    @3
    c1q
    crq
    cfv
    #
    @7
    cltq
    wbr
    @11
    @2
    c1q
    ltrnq
    @12
    c1q
    @7
    cltq
    @12
    c1q
    cmq
    co
    #
    c1q
    @12
    cmq
    co
    #
    @12
    c1q
    @12
    c1q
    mulcomnq
    c1q
    cnq
    wcel
    #
    @12
    cnq
    wcel
    @13
    @12
    wceq
    1nq
    c1q
    recclnq
    @12
    mulidnq
    mp2b
    @15
    @14
    c1q
    wceq
    1nq
    c1q
    recidnq
    ax-mp
    3eqtr3i
    breq1i
    bitri
    vv
    cA
    @7
    prlem936
    sylan2b
    @5
    @6
    cA
    wcel
    #
    @10
    wa
    #
    wa
    #
    @6
    vz
    cv
    #
    cltq
    wbr
    #
    vz
    cA
    wrex
    #
    @4
    @0
    @16
    @21
    @3
    @10
    vz
    cA
    @6
    prnmax
    ad2ant2r
    @18
    @21
    @2
    @19
    vx
    cv
    #
    cmq
    co
    #
    wceq
    #
    vx
    cB
    wrex
    #
    vz
    cA
    wrex
    #
    @4
    @18
    @20
    @25
    vz
    cA
    @5
    @17
    @20
    @25
    @5
    @17
    @20
    w3a
    #
    @19
    crq
    cfv
    #
    @2
    cmq
    co
    #
    cB
    wcel
    #
    @2
    @19
    @29
    cmq
    co
    #
    wceq
    #
    @25
    @27
    @6
    cnq
    wcel
    #
    @2
    cnq
    wcel
    #
    @20
    @10
    @30
    @5
    @17
    @33
    @20
    @0
    @16
    @33
    @3
    @10
    cA
    @6
    elprnq
    ad2ant2r
    3adant3
    @27
    @3
    @34
    @0
    @3
    @17
    @20
    simp1r
    @3
    @34
    @15
    @2
    c1q
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simpld
    syl
    #
    @5
    @17
    @20
    simp3
    @5
    @16
    @10
    @20
    simp2r
    @33
    @34
    wa
    #
    @20
    @10
    wa
    #
    @30
    @36
    @37
    @29
    @6
    crq
    cfv
    #
    @2
    cmq
    co
    #
    cltq
    wbr
    #
    @39
    crq
    cfv
    #
    cA
    wcel
    #
    wn
    #
    wa
    #
    @30
    @36
    @20
    @40
    @10
    @43
    @36
    @20
    @40
    @34
    @20
    @40
    wb
    @33
    @20
    @28
    @38
    cltq
    wbr
    @34
    @40
    @6
    @19
    ltrnq
    vx
    vy
    vu
    @28
    @38
    @2
    cltq
    cnq
    cmq
    @19
    crq
    fvex
    @6
    crq
    fvex
    #
    @22
    vy
    cv
    #
    vu
    cv
    #
    ltmnq
    vw
    vex
    #
    @22
    @46
    mulcomnq
    #
    caovord2
    syl5bb
    adantl
    biimpd
    @36
    @43
    @10
    @36
    @42
    @9
    @36
    @41
    @8
    cA
    @36
    @41
    @8
    wceq
    #
    @39
    @8
    cmq
    co
    #
    c1q
    wceq
    #
    @36
    @38
    @6
    cmq
    co
    #
    @2
    @7
    cmq
    co
    #
    cmq
    co
    c1q
    c1q
    cmq
    co
    #
    @51
    c1q
    @33
    @34
    @53
    c1q
    @54
    c1q
    cmq
    @33
    @53
    @6
    @38
    cmq
    co
    c1q
    @6
    @38
    mulcomnq
    @6
    recidnq
    syl5eqr
    @2
    recidnq
    oveqan12d
    vx
    vy
    vu
    @38
    @6
    @2
    @7
    cmq
    @45
    vv
    vex
    @48
    @49
    @22
    @46
    @47
    mulassnq
    @2
    crq
    fvex
    caov4
    @15
    @55
    c1q
    wceq
    1nq
    c1q
    mulidnq
    ax-mp
    3eqtr3g
    @36
    @39
    cnq
    wcel
    #
    @50
    @52
    wb
    @33
    @38
    cnq
    wcel
    @34
    @56
    @6
    recclnq
    @38
    @2
    mulclnq
    sylan
    @39
    @8
    recmulnq
    syl
    mpbird
    eleq1d
    notbid
    biimprd
    anim12d
    @44
    @29
    @46
    cltq
    wbr
    #
    @46
    crq
    cfv
    #
    cA
    wcel
    #
    wn
    #
    wa
    #
    vy
    wex
    #
    @30
    @61
    @44
    vy
    @39
    @38
    @2
    cmq
    ovex
    @46
    @39
    wceq
    #
    @57
    @40
    @60
    @43
    @46
    @39
    @29
    cltq
    breq2
    @63
    @59
    @42
    @63
    @58
    @41
    cA
    @46
    @39
    crq
    fveq2
    eleq1d
    notbid
    anbi12d
    spcev
    @22
    @46
    cltq
    wbr
    #
    @60
    wa
    #
    vy
    wex
    @62
    vx
    @29
    cB
    @28
    @2
    cmq
    ovex
    @22
    @29
    wceq
    #
    @65
    @61
    vy
    @66
    @64
    @57
    @60
    @22
    @29
    @46
    cltq
    breq1
    anbi1d
    exbidv
    reclempr.1
    elab2
    sylibr
    syl6
    imp
    syl22anc
    @27
    @19
    cnq
    wcel
    #
    @34
    @32
    @20
    @5
    @67
    @17
    @20
    @33
    @67
    @6
    @19
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simprd
    3ad2ant3
    @35
    @34
    @67
    @2
    c1q
    @2
    cmq
    co
    #
    @31
    @34
    @68
    @2
    c1q
    cmq
    co
    @2
    @2
    c1q
    mulcomnq
    @2
    mulidnq
    syl5reqr
    @67
    @31
    @19
    @28
    cmq
    co
    #
    @2
    cmq
    co
    @68
    @19
    @28
    @2
    mulassnq
    @67
    @69
    c1q
    @2
    cmq
    @19
    recidnq
    oveq1d
    syl5reqr
    sylan9eqr
    syl2anc
    @24
    @32
    vx
    @29
    cB
    @66
    @23
    @31
    @2
    @22
    @29
    @19
    cmq
    oveq2
    eqeq2d
    rspcev
    syl2anc
    3expia
    reximdv
    @0
    @4
    @26
    wb
    #
    @3
    @17
    @0
    cB
    cnp
    wcel
    @70
    vx
    vy
    cA
    cB
    reclempr.1
    reclem2pr
    vu
    vf
    vg
    vy
    vw
    cA
    cB
    @2
    vz
    vx
    cmp
    cmq
    vy
    vw
    vu
    vf
    vg
    df-mp
    vf
    cv
    vg
    cv
    mulclnq
    genpelv
    mpdan
    ad2antrr
    sylibrd
    mpd
    rexlimddv
    ex
    syl5bi
    ssrdv
end
