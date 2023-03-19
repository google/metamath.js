include "cnp.mm"
include "wcel.mm"
include "cmp.mm"
include "co.mm"
include "c1p.mm"
include "cv.mm"
include "c1q.mm"
include "cltq.mm"
include "wbr.mm"
include "cmq.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "reclem2pr.mm"
include "df-mp.mm"
include "mulclnq.mm"
include "genpelv.mm"
include "mpdan.mm"
include "wi.mm"
include "wa.mm"
include "crq.mm"
include "cfv.mm"
include "wn.mm"
include "wex.mm"
include "abeq2i.mm"
include "cnq.mm"
include "ltrelnq.mm"
include "brel.mm"
include "simprd.mm"
include "elprnq.mm"
include "ltmnq.mm"
include "syl.mm"
include "biimpd.mm"
include "adantr.mm"
include "recclnq.mm"
include "prub.mm"
include "sylan2.mm"
include "mulcomnq.mm"
include "a1i.mm"
include "recidnq.mm"
include "breq12d.mm"
include "bitrd.mm"
include "adantl.mm"
include "sylibd.mm"
include "anim12d.mm"
include "ltsonq.mm"
include "sotri.mm"
include "syl6.mm"
include "exp4b.mm"
include "syl5.mm"
include "pm2.43d.mm"
include "impd.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "breq1.mm"
include "biimprcd.mm"
include "expimpd.mm"
include "rexlimdvv.mm"
include "sylbid.mm"
include "df-1p.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "reclem3pr.mm"
include "eqssd.mm"

theorem reclem4pr
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
  assert |- ( A e. P. -> ( A .P. B ) = 1P )

  proof
    cA
    cnp
    wcel
    #
    cA
    cB
    cmp
    co
    #
    c1p
    @0
    vw
    @1
    c1p
    @0
    vw
    cv
    #
    @1
    wcel
    #
    @2
    c1q
    cltq
    wbr
    #
    @2
    c1p
    wcel
    @0
    @3
    @2
    vz
    cv
    #
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
    vz
    cA
    wrex
    #
    @4
    @0
    cB
    cnp
    wcel
    @3
    @9
    wb
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
    @0
    @8
    @4
    vz
    vx
    cA
    cB
    @0
    @5
    cA
    wcel
    #
    @6
    cB
    wcel
    #
    @8
    @4
    wi
    #
    @0
    @10
    wa
    #
    @11
    @7
    c1q
    cltq
    wbr
    #
    @12
    @11
    @6
    vy
    cv
    #
    cltq
    wbr
    #
    @15
    crq
    cfv
    #
    cA
    wcel
    wn
    #
    wa
    #
    vy
    wex
    #
    @13
    @14
    @20
    vx
    cB
    reclempr.1
    abeq2i
    @13
    @19
    @14
    vy
    @13
    @16
    @18
    @14
    @13
    @16
    @18
    @14
    wi
    #
    @16
    @15
    cnq
    wcel
    #
    @13
    @16
    @21
    wi
    @16
    @6
    cnq
    wcel
    @22
    @6
    @15
    cnq
    cnq
    cltq
    ltrelnq
    brel
    simprd
    @13
    @22
    @16
    @18
    @14
    @13
    @22
    wa
    #
    @19
    @7
    @5
    @15
    cmq
    co
    #
    cltq
    wbr
    #
    @24
    c1q
    cltq
    wbr
    #
    wa
    @14
    @23
    @16
    @25
    @18
    @26
    @13
    @16
    @25
    wi
    @22
    @13
    @16
    @25
    @13
    @5
    cnq
    wcel
    @16
    @25
    wb
    cA
    @5
    elprnq
    @6
    @15
    @5
    ltmnq
    syl
    biimpd
    adantr
    @23
    @18
    @5
    @17
    cltq
    wbr
    #
    @26
    @22
    @13
    @17
    cnq
    wcel
    @18
    @27
    wi
    @15
    recclnq
    cA
    @5
    @17
    prub
    sylan2
    @22
    @27
    @26
    wb
    @13
    @22
    @27
    @15
    @5
    cmq
    co
    #
    @15
    @17
    cmq
    co
    #
    cltq
    wbr
    @26
    @5
    @17
    @15
    ltmnq
    @22
    @28
    @24
    @29
    c1q
    cltq
    @28
    @24
    wceq
    @22
    @15
    @5
    mulcomnq
    a1i
    @15
    recidnq
    breq12d
    bitrd
    adantl
    sylibd
    anim12d
    @7
    @24
    c1q
    cltq
    cnq
    ltsonq
    ltrelnq
    sotri
    syl6
    exp4b
    syl5
    pm2.43d
    impd
    exlimdv
    syl5bi
    @8
    @4
    @14
    @2
    @7
    c1q
    cltq
    breq1
    biimprcd
    syl6
    expimpd
    rexlimdvv
    sylbid
    @4
    vw
    c1p
    vw
    df-1p
    abeq2i
    syl6ibr
    ssrdv
    vx
    vy
    cA
    cB
    reclempr.1
    reclem3pr
    eqssd
end
