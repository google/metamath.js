include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wa.mm"
include "refldivcl.mm"
include "peano2re.mm"
include "syl.mm"
include "3adant3.mm"
include "adantr.mm"
include "rerpdivcl.mm"
include "ancoms.mm"
include "3adant1.mm"
include "1red.mm"
include "cle.mm"
include "3simpa.mm"
include "fldivle.mm"
include "leadd1dd.mm"
include "cmul.mm"
include "wb.mm"
include "rpre.mm"
include "ltaddsub.mm"
include "syl3an2.mm"
include "biimpar.mm"
include "cc.mm"
include "recn.mm"
include "1cnd.mm"
include "rpcn.mm"
include "3ad2ant2.mm"
include "adddird.mm"
include "3ad2ant1.mm"
include "cc0.mm"
include "wne.mm"
include "rpne0.mm"
include "divcan1d.mm"
include "wceq.mm"
include "mulid2d.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "3ad2ant3.mm"
include "breq12d.mm"
include "mpbird.mm"
include "simp2.mm"
include "ltmul1d.mm"
include "lelttrd.mm"
include "ex.mm"

theorem ltdifltdiv
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR+ /\ C e. RR ) -> ( A < ( C - B ) -> ( ( |_ ` ( A / B ) ) + 1 ) < ( C / B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cA
    cC
    cB
    cmin
    co
    clt
    wbr
    #
    cA
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cC
    cB
    cdiv
    co
    #
    clt
    wbr
    @3
    @4
    wa
    #
    @7
    @5
    c1
    caddc
    co
    #
    @8
    @3
    @7
    cr
    wcel
    #
    @4
    @0
    @1
    @11
    @2
    @0
    @1
    wa
    #
    @6
    cr
    wcel
    #
    @11
    cA
    cB
    refldivcl
    #
    @6
    peano2re
    syl
    3adant3
    adantr
    @3
    @10
    cr
    wcel
    #
    @4
    @0
    @1
    @15
    @2
    @12
    @5
    cr
    wcel
    #
    @15
    cA
    cB
    rerpdivcl
    #
    @5
    peano2re
    #
    syl
    3adant3
    adantr
    @3
    @8
    cr
    wcel
    #
    @4
    @1
    @2
    @19
    @0
    @2
    @1
    @19
    cC
    cB
    rerpdivcl
    ancoms
    3adant1
    #
    adantr
    @9
    @6
    @5
    c1
    @3
    @13
    @4
    @0
    @1
    @13
    @2
    @14
    3adant3
    adantr
    @3
    @16
    @4
    @0
    @1
    @16
    @2
    @17
    3adant3
    #
    adantr
    @9
    1red
    @9
    @12
    @6
    @5
    cle
    wbr
    @3
    @12
    @4
    @0
    @1
    @2
    3simpa
    adantr
    cA
    cB
    fldivle
    syl
    leadd1dd
    @9
    @10
    @8
    clt
    wbr
    #
    @10
    cB
    cmul
    co
    #
    @8
    cB
    cmul
    co
    #
    clt
    wbr
    #
    @9
    @25
    cA
    cB
    caddc
    co
    #
    cC
    clt
    wbr
    #
    @3
    @27
    @4
    @1
    @0
    cB
    cr
    wcel
    @2
    @27
    @4
    wb
    cB
    rpre
    cA
    cB
    cC
    ltaddsub
    syl3an2
    biimpar
    @3
    @25
    @27
    wb
    @4
    @3
    @23
    @26
    @24
    cC
    clt
    @3
    @23
    @5
    cB
    cmul
    co
    #
    c1
    cB
    cmul
    co
    #
    caddc
    co
    @26
    @3
    @5
    c1
    cB
    @0
    @1
    @5
    cc
    wcel
    #
    @2
    @12
    @16
    @30
    @17
    @5
    recn
    syl
    3adant3
    @3
    1cnd
    @1
    @0
    cB
    cc
    wcel
    @2
    cB
    rpcn
    #
    3ad2ant2
    #
    adddird
    @3
    @28
    cA
    @29
    cB
    caddc
    @3
    cA
    cB
    @0
    @1
    cA
    cc
    wcel
    @2
    cA
    recn
    3ad2ant1
    @32
    @1
    @0
    cB
    cc0
    wne
    @2
    cB
    rpne0
    3ad2ant2
    #
    divcan1d
    @1
    @0
    @29
    cB
    wceq
    @2
    @1
    cB
    @31
    mulid2d
    3ad2ant2
    oveq12d
    eqtrd
    @3
    cC
    cB
    @2
    @0
    cC
    cc
    wcel
    @1
    cC
    recn
    3ad2ant3
    @32
    @33
    divcan1d
    breq12d
    adantr
    mpbird
    @3
    @22
    @25
    wb
    @4
    @3
    @10
    @8
    cB
    @3
    @16
    @15
    @21
    @18
    syl
    @20
    @0
    @1
    @2
    simp2
    ltmul1d
    adantr
    mpbird
    lelttrd
    ex
end
