include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "cxne.mm"
include "cr.mm"
include "cpnf.mm"
include "wceq.mm"
include "cmnf.mm"
include "w3o.mm"
include "wa.mm"
include "wi.mm"
include "elxr.mm"
include "cneg.mm"
include "ltneg.mm"
include "rexneg.mm"
include "breqan12rd.mm"
include "bitr4d.mm"
include "biimpd.mm"
include "xnegeq.mm"
include "xnegpnf.mm"
include "syl6eq.mm"
include "adantl.mm"
include "renegcl.mm"
include "eqeltrd.mm"
include "mnflt.mm"
include "syl.mm"
include "adantr.mm"
include "eqbrtrd.mm"
include "a1d.mm"
include "simpr.mm"
include "breq2d.mm"
include "wn.mm"
include "rexr.mm"
include "nltmnf.mm"
include "pm2.21d.mm"
include "sylbid.mm"
include "3jaodan.mm"
include "sylan2b.mm"
include "expimpd.mm"
include "simpl.mm"
include "breq1d.mm"
include "pnfnlt.mm"
include "breq1.mm"
include "anbi2d.mm"
include "ltpnf.mm"
include "mnfltpnf.mm"
include "syl6eqbr.mm"
include "breq2.mm"
include "mnfxr.mm"
include "ax-mp.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "imp.mm"
include "3jaoian.mm"
include "sylanb.mm"
include "xnegmnf.mm"
include "syl5ibr.mm"
include "3jaoi.mm"
include "sylbi.mm"
include "3impib.mm"

theorem xltnegi
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* /\ A < B ) -> -e B < -e A )

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
    cB
    cxne
    #
    cA
    cxne
    #
    clt
    wbr
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
    @1
    @2
    wa
    #
    @5
    wi
    #
    cA
    elxr
    @6
    @10
    @7
    @8
    @6
    @1
    @2
    @5
    @1
    @6
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
    @2
    @5
    wi
    #
    cB
    elxr
    #
    @6
    @11
    @15
    @12
    @13
    @6
    @11
    wa
    #
    @2
    @5
    @17
    @2
    cB
    cneg
    #
    cA
    cneg
    #
    clt
    wbr
    @5
    cA
    cB
    ltneg
    @11
    @6
    @3
    @18
    @4
    @19
    clt
    cB
    rexneg
    #
    cA
    rexneg
    #
    breqan12rd
    bitr4d
    biimpd
    @6
    @12
    wa
    #
    @5
    @2
    @22
    @3
    cmnf
    @4
    clt
    @12
    @3
    cmnf
    wceq
    #
    @6
    @12
    @3
    cpnf
    cxne
    cmnf
    cB
    cpnf
    xnegeq
    xnegpnf
    syl6eq
    #
    adantl
    @6
    cmnf
    @4
    clt
    wbr
    #
    @12
    @6
    @4
    cr
    wcel
    @25
    @6
    @4
    @19
    cr
    @21
    cA
    renegcl
    eqeltrd
    @4
    mnflt
    syl
    adantr
    eqbrtrd
    a1d
    @6
    @13
    wa
    #
    @2
    cA
    cmnf
    clt
    wbr
    #
    @5
    @26
    cB
    cmnf
    cA
    clt
    @6
    @13
    simpr
    breq2d
    @26
    @27
    @5
    @6
    @27
    wn
    #
    @13
    @6
    @0
    @28
    cA
    rexr
    cA
    nltmnf
    syl
    adantr
    pm2.21d
    sylbid
    3jaodan
    sylan2b
    expimpd
    @7
    @1
    @2
    @5
    @7
    @1
    wa
    #
    @2
    cpnf
    cB
    clt
    wbr
    #
    @5
    @29
    cA
    cpnf
    cB
    clt
    @7
    @1
    simpl
    breq1d
    @29
    @30
    @5
    @1
    @30
    wn
    @7
    cB
    pnfnlt
    adantl
    pm2.21d
    sylbid
    expimpd
    @8
    @9
    @1
    cmnf
    cB
    clt
    wbr
    #
    wa
    #
    @5
    @8
    @2
    @31
    @1
    cA
    cmnf
    cB
    clt
    breq1
    anbi2d
    @32
    @5
    @8
    @3
    cpnf
    clt
    wbr
    #
    @1
    @14
    @31
    @33
    @16
    @11
    @31
    @33
    @12
    @13
    @11
    @31
    wa
    @3
    cr
    wcel
    #
    @33
    @11
    @34
    @31
    @11
    @3
    @18
    cr
    @20
    cB
    renegcl
    eqeltrd
    adantr
    @3
    ltpnf
    syl
    @12
    @31
    wa
    @3
    cmnf
    cpnf
    clt
    @12
    @23
    @31
    @24
    adantr
    mnfltpnf
    syl6eqbr
    @13
    @31
    @33
    @13
    @31
    cmnf
    cmnf
    clt
    wbr
    #
    @33
    cB
    cmnf
    cmnf
    clt
    breq2
    @35
    @33
    cmnf
    cxr
    wcel
    @35
    wn
    mnfxr
    cmnf
    nltmnf
    ax-mp
    pm2.21i
    syl6bi
    imp
    3jaoian
    sylanb
    @8
    @4
    cpnf
    @3
    clt
    @8
    @4
    cmnf
    cxne
    cpnf
    cA
    cmnf
    xnegeq
    xnegmnf
    syl6eq
    breq2d
    syl5ibr
    sylbid
    3jaoi
    sylbi
    3impib
end
