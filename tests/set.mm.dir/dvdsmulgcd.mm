include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cgcd.mm"
include "cv.mm"
include "caddc.mm"
include "wceq.mm"
include "wrex.mm"
include "simplr.mm"
include "dvdszrcl.mm"
include "adantl.mm"
include "simpld.mm"
include "bezout.mm"
include "syl2anc.mm"
include "adantr.mm"
include "simplll.mm"
include "simpllr.mm"
include "simprl.mm"
include "zmulcld.mm"
include "simprr.mm"
include "wi.mm"
include "dvdsmultr1.mm"
include "syl3anc.mm"
include "mpd.mm"
include "zcnd.mm"
include "mulassd.mm"
include "breqtrd.mm"
include "dvdsmul1.mm"
include "mul12d.mm"
include "breqtrrd.mm"
include "w3a.mm"
include "dvds2add.mm"
include "imp.mm"
include "syl32anc.mm"
include "adddid.mm"
include "oveq2.mm"
include "breq2d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "simprd.mm"
include "zmulcl.mm"
include "simpr.mm"
include "gcddvds.mm"
include "gcdcld.mm"
include "nn0zd.mm"
include "simpll.mm"
include "dvdscmul.mm"
include "dvdstr.mm"
include "impbida.mm"

theorem dvdsmulgcd
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( B e. ZZ /\ C e. ZZ ) -> ( A || ( B x. C ) <-> A || ( B x. ( C gcd A ) ) ) )

  proof
    cB
    cz
    wcel
    #
    cC
    cz
    wcel
    #
    wa
    #
    cA
    cB
    cC
    cmul
    co
    #
    cdvds
    wbr
    #
    cA
    cB
    cC
    cA
    cgcd
    co
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    @2
    @4
    wa
    #
    @5
    cC
    vx
    cv
    #
    cmul
    co
    #
    cA
    vy
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vy
    cz
    wrex
    vx
    cz
    wrex
    #
    @7
    @8
    @1
    cA
    cz
    wcel
    #
    @15
    @0
    @1
    @4
    simplr
    @8
    @16
    @3
    cz
    wcel
    #
    @4
    @16
    @17
    wa
    @2
    cA
    @3
    dvdszrcl
    adantl
    simpld
    #
    vx
    vy
    cC
    cA
    bezout
    syl2anc
    @8
    @14
    @7
    vx
    vy
    cz
    cz
    @8
    @9
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    wa
    #
    wa
    #
    @7
    @14
    cA
    cB
    @13
    cmul
    co
    #
    cdvds
    wbr
    @22
    cA
    cB
    @10
    cmul
    co
    #
    cB
    @12
    cmul
    co
    #
    caddc
    co
    #
    @23
    cdvds
    @22
    @16
    @24
    cz
    wcel
    #
    @25
    cz
    wcel
    #
    cA
    @24
    cdvds
    wbr
    #
    cA
    @25
    cdvds
    wbr
    #
    cA
    @26
    cdvds
    wbr
    #
    @8
    @16
    @21
    @18
    adantr
    #
    @22
    cB
    @10
    @0
    @1
    @4
    @21
    simplll
    #
    @22
    cC
    @9
    @0
    @1
    @4
    @21
    simpllr
    #
    @8
    @19
    @20
    simprl
    #
    zmulcld
    #
    zmulcld
    @22
    cB
    @12
    @33
    @22
    cA
    @11
    @32
    @8
    @19
    @20
    simprr
    #
    zmulcld
    #
    zmulcld
    @22
    cA
    @3
    @9
    cmul
    co
    #
    @24
    cdvds
    @22
    @4
    cA
    @39
    cdvds
    wbr
    #
    @2
    @4
    @21
    simplr
    @22
    @16
    @17
    @19
    @4
    @40
    wi
    @32
    @22
    cB
    cC
    @33
    @34
    zmulcld
    @35
    cA
    @3
    @9
    dvdsmultr1
    syl3anc
    mpd
    @22
    cB
    cC
    @9
    @22
    cB
    @33
    zcnd
    #
    @22
    cC
    @34
    zcnd
    @22
    @9
    @35
    zcnd
    mulassd
    breqtrd
    @22
    cA
    cA
    cB
    @11
    cmul
    co
    #
    cmul
    co
    #
    @25
    cdvds
    @22
    @16
    @42
    cz
    wcel
    cA
    @43
    cdvds
    wbr
    @32
    @22
    cB
    @11
    @33
    @37
    zmulcld
    cA
    @42
    dvdsmul1
    syl2anc
    @22
    cB
    cA
    @11
    @41
    @22
    cA
    @32
    zcnd
    @22
    @11
    @37
    zcnd
    mul12d
    breqtrrd
    @16
    @27
    @28
    w3a
    @29
    @30
    wa
    @31
    cA
    @24
    @25
    dvds2add
    imp
    syl32anc
    @22
    cB
    @10
    @12
    @41
    @22
    @10
    @36
    zcnd
    @22
    @12
    @38
    zcnd
    adddid
    breqtrrd
    @14
    @6
    @23
    cA
    cdvds
    @5
    @13
    cB
    cmul
    oveq2
    breq2d
    syl5ibrcom
    rexlimdvva
    mpd
    @2
    @7
    wa
    #
    @16
    @6
    cz
    wcel
    #
    @17
    @7
    @6
    @3
    cdvds
    wbr
    #
    @4
    @44
    @16
    @45
    @7
    @16
    @45
    wa
    @2
    cA
    @6
    dvdszrcl
    adantl
    #
    simpld
    #
    @44
    @16
    @45
    @47
    simprd
    @2
    @17
    @7
    cB
    cC
    zmulcl
    adantr
    @2
    @7
    simpr
    @44
    @5
    cC
    cdvds
    wbr
    #
    @46
    @44
    @49
    @5
    cA
    cdvds
    wbr
    #
    @44
    @1
    @16
    @49
    @50
    wa
    @0
    @1
    @7
    simplr
    #
    @48
    cC
    cA
    gcddvds
    syl2anc
    simpld
    @44
    @5
    cz
    wcel
    @1
    @0
    @49
    @46
    wi
    @44
    @5
    @44
    cC
    cA
    @51
    @48
    gcdcld
    nn0zd
    @51
    @0
    @1
    @7
    simpll
    cB
    @5
    cC
    dvdscmul
    syl3anc
    mpd
    @16
    @45
    @17
    w3a
    @7
    @46
    wa
    @4
    cA
    @6
    @3
    dvdstr
    imp
    syl32anc
    impbida
end
