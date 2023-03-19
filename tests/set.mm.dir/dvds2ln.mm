include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cv.mm"
include "simpr1.mm"
include "simpr2.mm"
include "jca.mm"
include "simpr3.mm"
include "simpll.mm"
include "zmulcld.mm"
include "simplr.mm"
include "zaddcld.mm"
include "wi.mm"
include "zmulcl.mm"
include "anim12i.mm"
include "an4s.mm"
include "expcom.mm"
include "adantr.mm"
include "imp.mm"
include "zaddcl.mm"
include "syl.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "zcnd.mm"
include "adddir.mm"
include "3expa.mm"
include "syl2anc.mm"
include "adantl.mm"
include "ad3antrrr.mm"
include "mul32d.mm"
include "oveq12d.mm"
include "mulcld.mm"
include "mulcomd.mm"
include "3eqtrd.mm"
include "oveq2.mm"
include "oveqan12d.mm"
include "sylan9eq.mm"
include "ex.mm"
include "dvds2lem.mm"

theorem dvds2ln
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ( I e. ZZ /\ J e. ZZ ) /\ ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) ) -> ( ( K || M /\ K || N ) -> K || ( ( I x. M ) + ( J x. N ) ) ) )

  proof
    cI
    cz
    wcel
    #
    cJ
    cz
    wcel
    #
    wa
    #
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    wa
    #
    vx
    vy
    cK
    cM
    cK
    cN
    cK
    cI
    cM
    cmul
    co
    #
    cJ
    cN
    cmul
    co
    #
    caddc
    co
    #
    vx
    cv
    #
    cI
    cmul
    co
    #
    vy
    cv
    #
    cJ
    cmul
    co
    #
    caddc
    co
    #
    @7
    @3
    @4
    @2
    @3
    @4
    @5
    simpr1
    #
    @2
    @3
    @4
    @5
    simpr2
    #
    jca
    @7
    @3
    @5
    @16
    @2
    @3
    @4
    @5
    simpr3
    #
    jca
    @7
    @3
    @10
    cz
    wcel
    @16
    @7
    @8
    @9
    @7
    cI
    cM
    @0
    @1
    @6
    simpll
    @17
    zmulcld
    @7
    cJ
    cN
    @0
    @1
    @6
    simplr
    #
    @18
    zmulcld
    zaddcld
    jca
    @7
    @11
    cz
    wcel
    #
    @13
    cz
    wcel
    #
    wa
    #
    wa
    #
    @12
    cz
    wcel
    #
    @14
    cz
    wcel
    #
    wa
    #
    @15
    cz
    wcel
    @7
    @22
    @26
    @2
    @22
    @26
    wi
    @6
    @22
    @2
    @26
    @20
    @0
    @21
    @1
    @26
    @20
    @0
    wa
    @24
    @21
    @1
    wa
    @25
    @11
    cI
    zmulcl
    @13
    cJ
    zmulcl
    anim12i
    an4s
    expcom
    adantr
    imp
    #
    @12
    @14
    zaddcl
    syl
    @23
    @11
    cK
    cmul
    co
    #
    cM
    wceq
    #
    @13
    cK
    cmul
    co
    #
    cN
    wceq
    #
    wa
    #
    @15
    cK
    cmul
    co
    #
    @10
    wceq
    @23
    @32
    @33
    cI
    @28
    cmul
    co
    #
    cJ
    @30
    cmul
    co
    #
    caddc
    co
    #
    @10
    @23
    @33
    @12
    cK
    cmul
    co
    #
    @14
    cK
    cmul
    co
    #
    caddc
    co
    #
    @28
    cI
    cmul
    co
    #
    @30
    cJ
    cmul
    co
    #
    caddc
    co
    @36
    @23
    @12
    cc
    wcel
    #
    @14
    cc
    wcel
    #
    wa
    #
    cK
    cc
    wcel
    #
    @33
    @39
    wceq
    #
    @23
    @26
    @44
    @27
    @24
    @42
    @25
    @43
    @12
    zcn
    @14
    zcn
    anim12i
    syl
    @7
    @45
    @22
    @7
    cK
    @16
    zcnd
    adantr
    #
    @42
    @43
    @45
    @46
    @12
    @14
    cK
    adddir
    3expa
    syl2anc
    @23
    @37
    @40
    @38
    @41
    caddc
    @23
    @11
    cI
    cK
    @22
    @11
    cc
    wcel
    #
    @7
    @20
    @48
    @21
    @11
    zcn
    adantr
    adantl
    #
    @0
    cI
    cc
    wcel
    @1
    @6
    @22
    cI
    zcn
    ad3antrrr
    #
    @47
    mul32d
    @23
    @13
    cJ
    cK
    @22
    @13
    cc
    wcel
    #
    @7
    @21
    @51
    @20
    @13
    zcn
    adantl
    adantl
    #
    @7
    cJ
    cc
    wcel
    @22
    @7
    cJ
    @19
    zcnd
    adantr
    #
    @47
    mul32d
    oveq12d
    @23
    @40
    @34
    @41
    @35
    caddc
    @23
    @28
    cI
    @23
    @11
    cK
    @49
    @47
    mulcld
    @50
    mulcomd
    @23
    @30
    cJ
    @23
    @13
    cK
    @52
    @47
    mulcld
    @53
    mulcomd
    oveq12d
    3eqtrd
    @29
    @31
    @34
    @8
    @35
    @9
    caddc
    @28
    cM
    cI
    cmul
    oveq2
    @30
    cN
    cJ
    cmul
    oveq2
    oveqan12d
    sylan9eq
    ex
    dvds2lem
end
