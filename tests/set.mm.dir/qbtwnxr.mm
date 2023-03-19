include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "cq.mm"
include "wrex.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "wi.mm"
include "elxr.mm"
include "qbtwnre.mm"
include "3expia.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "simpl.mm"
include "peano2re.mm"
include "adantr.mm"
include "ltp1.mm"
include "syl3anc.mm"
include "qre.mm"
include "ltpnf.mm"
include "syl.mm"
include "adantl.mm"
include "simplr.mm"
include "breqtrrd.mm"
include "a1d.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"
include "rexr.mm"
include "wb.mm"
include "breq2.mm"
include "wn.mm"
include "nltmnf.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "sylan.mm"
include "3jaodan.mm"
include "sylan2b.mm"
include "breq1.mm"
include "pnfnlt.mm"
include "cmin.mm"
include "peano2rem.mm"
include "simpr.mm"
include "ltm1.mm"
include "simpll.mm"
include "mnflt.mm"
include "eqbrtrd.mm"
include "anim1d.mm"
include "1re.mm"
include "ax-mp.mm"
include "mpbiri.mm"
include "cz.mm"
include "1z.mm"
include "zq.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpan.mm"
include "syl2an.mm"
include "3mix3.mm"
include "sylibr.mm"
include "3jaoian.mm"
include "sylanb.mm"
include "3impia.mm"

theorem qbtwnxr
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
  assert |- ( ( A e. RR* /\ B e. RR* /\ A < B ) -> E. x e. QQ ( A < x /\ x < B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
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
    cA
    cr
    wcel
    #
    cA
    cpnf
    wceq
    #
    cA
    cmnf
    wceq
    #
    w3o
    #
    @1
    @2
    @7
    wi
    #
    cA
    elxr
    #
    @8
    @1
    @12
    @9
    @10
    @1
    @8
    cB
    cr
    wcel
    #
    cB
    cpnf
    wceq
    #
    cB
    cmnf
    wceq
    #
    w3o
    #
    @12
    cB
    elxr
    #
    @8
    @14
    @12
    @15
    @16
    @8
    @14
    @2
    @7
    vx
    cA
    cB
    qbtwnre
    3expia
    @8
    @15
    wa
    #
    @7
    @2
    @19
    @4
    @3
    cA
    c1
    caddc
    co
    #
    clt
    wbr
    #
    wa
    #
    vx
    cq
    wrex
    #
    @7
    @19
    @8
    @20
    cr
    wcel
    #
    cA
    @20
    clt
    wbr
    #
    @23
    @8
    @15
    simpl
    @8
    @24
    @15
    cA
    peano2re
    adantr
    @8
    @25
    @15
    cA
    ltp1
    adantr
    vx
    cA
    @20
    qbtwnre
    syl3anc
    @19
    @22
    @6
    vx
    cq
    @19
    @3
    cq
    wcel
    #
    wa
    #
    @21
    @5
    @4
    @27
    @5
    @21
    @27
    @3
    cpnf
    cB
    clt
    @26
    @3
    cpnf
    clt
    wbr
    #
    @19
    @26
    @3
    cr
    wcel
    #
    @28
    @3
    qre
    #
    @3
    ltpnf
    syl
    adantl
    @8
    @15
    @26
    simplr
    breqtrrd
    a1d
    anim2d
    reximdva
    mpd
    a1d
    @8
    @0
    @16
    @12
    cA
    rexr
    @0
    @16
    wa
    #
    @2
    cA
    cmnf
    clt
    wbr
    #
    @7
    @16
    @2
    @32
    wb
    @0
    cB
    cmnf
    cA
    clt
    breq2
    adantl
    @31
    @32
    @7
    @0
    @32
    wn
    @16
    cA
    nltmnf
    adantr
    pm2.21d
    sylbid
    #
    sylan
    3jaodan
    sylan2b
    @9
    @1
    wa
    #
    @2
    cpnf
    cB
    clt
    wbr
    #
    @7
    @9
    @2
    @35
    wb
    @1
    cA
    cpnf
    cB
    clt
    breq1
    adantr
    @34
    @35
    @7
    @1
    @35
    wn
    @9
    cB
    pnfnlt
    adantl
    pm2.21d
    sylbid
    @1
    @10
    @17
    @12
    @18
    @10
    @14
    @12
    @15
    @16
    @10
    @14
    wa
    #
    @7
    @2
    @36
    cB
    c1
    cmin
    co
    #
    @3
    clt
    wbr
    #
    @5
    wa
    #
    vx
    cq
    wrex
    #
    @7
    @36
    @37
    cr
    wcel
    #
    @14
    @37
    cB
    clt
    wbr
    #
    @40
    @14
    @41
    @10
    cB
    peano2rem
    adantl
    @10
    @14
    simpr
    @14
    @42
    @10
    cB
    ltm1
    adantl
    vx
    @37
    cB
    qbtwnre
    syl3anc
    @36
    @39
    @6
    vx
    cq
    @36
    @26
    wa
    #
    @38
    @4
    @5
    @43
    @4
    @38
    @43
    cA
    cmnf
    @3
    clt
    @10
    @14
    @26
    simpll
    @43
    @29
    cmnf
    @3
    clt
    wbr
    @26
    @29
    @36
    @30
    adantl
    @3
    mnflt
    syl
    eqbrtrd
    a1d
    anim1d
    reximdva
    mpd
    a1d
    @10
    @15
    wa
    @7
    @2
    @10
    cA
    c1
    clt
    wbr
    #
    c1
    cB
    clt
    wbr
    #
    @7
    @15
    @10
    @44
    cmnf
    c1
    clt
    wbr
    #
    c1
    cr
    wcel
    #
    @46
    1re
    c1
    mnflt
    ax-mp
    cA
    cmnf
    c1
    clt
    breq1
    mpbiri
    @15
    @45
    c1
    cpnf
    clt
    wbr
    #
    @47
    @48
    1re
    c1
    ltpnf
    ax-mp
    cB
    cpnf
    c1
    clt
    breq2
    mpbiri
    c1
    cq
    wcel
    #
    @44
    @45
    wa
    #
    @7
    c1
    cz
    wcel
    @49
    1z
    c1
    zq
    ax-mp
    @6
    @50
    vx
    c1
    cq
    @3
    c1
    wceq
    @4
    @44
    @5
    @45
    @3
    c1
    cA
    clt
    breq2
    @3
    c1
    cB
    clt
    breq1
    anbi12d
    rspcev
    mpan
    syl2an
    a1d
    @10
    @0
    @16
    @12
    @10
    @11
    @0
    @10
    @8
    @9
    3mix3
    @13
    sylibr
    @33
    sylan
    3jaodan
    sylan2b
    3jaoian
    sylanb
    3impia
end
