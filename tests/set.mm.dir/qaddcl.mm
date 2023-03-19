include "cq.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "caddc.mm"
include "elq.mm"
include "wa.mm"
include "wi.mm"
include "cmul.mm"
include "nnz.mm"
include "zmulcl.mm"
include "sylan2.mm"
include "ad2ant2rl.mm"
include "simpl.mm"
include "adantl.mm"
include "syl2anr.mm"
include "zaddcld.mm"
include "adantr.mm"
include "nnmulcl.mm"
include "ad2ant2l.mm"
include "oveq12.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "zcn.mm"
include "anim12i.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "divadddiv.mm"
include "syl2an.mm"
include "an4s.mm"
include "sylan9eqr.mm"
include "w3a.mm"
include "rspceov.mm"
include "sylibr.mm"
include "syl3anc.mm"
include "exp43.mm"
include "rexlimivv.mm"
include "rexlimdvv.mm"
include "imp.mm"
include "syl2anb.mm"

theorem qaddcl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- ( ( A e. QQ /\ B e. QQ ) -> ( A + B ) e. QQ )

  proof
    cA
    cq
    wcel
    cA
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vy
    cn
    wrex
    vx
    cz
    wrex
    #
    cB
    vz
    cv
    #
    vw
    cv
    #
    cdiv
    co
    #
    wceq
    #
    vw
    cn
    wrex
    vz
    cz
    wrex
    #
    cA
    cB
    caddc
    co
    #
    cq
    wcel
    #
    cB
    cq
    wcel
    vx
    vy
    cA
    elq
    vz
    vw
    cB
    elq
    @4
    @9
    @11
    @4
    @8
    @11
    vz
    vw
    cz
    cn
    @3
    @5
    cz
    wcel
    #
    @6
    cn
    wcel
    #
    wa
    #
    @8
    @11
    wi
    wi
    vx
    vy
    cz
    cn
    @0
    cz
    wcel
    #
    @1
    cn
    wcel
    #
    wa
    #
    @3
    @14
    @8
    @11
    @17
    @14
    @3
    @8
    @11
    @17
    @14
    wa
    #
    @3
    @8
    wa
    #
    wa
    @0
    @6
    cmul
    co
    #
    @5
    @1
    cmul
    co
    #
    caddc
    co
    #
    cz
    wcel
    #
    @1
    @6
    cmul
    co
    #
    cn
    wcel
    #
    @10
    @22
    @24
    cdiv
    co
    #
    wceq
    #
    @11
    @18
    @23
    @19
    @18
    @20
    @21
    @15
    @13
    @20
    cz
    wcel
    #
    @16
    @12
    @13
    @15
    @6
    cz
    wcel
    @28
    @6
    nnz
    @0
    @6
    zmulcl
    sylan2
    ad2ant2rl
    @14
    @12
    @1
    cz
    wcel
    #
    @21
    cz
    wcel
    @17
    @12
    @13
    simpl
    @16
    @29
    @15
    @1
    nnz
    adantl
    @5
    @1
    zmulcl
    syl2anr
    zaddcld
    adantr
    @18
    @25
    @19
    @16
    @13
    @25
    @15
    @12
    @1
    @6
    nnmulcl
    ad2ant2l
    adantr
    @19
    @18
    @10
    @2
    @7
    caddc
    co
    #
    @26
    cA
    @2
    cB
    @7
    caddc
    oveq12
    @15
    @12
    @16
    @13
    @30
    @26
    wceq
    #
    @15
    @12
    wa
    @0
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    wa
    @1
    cc
    wcel
    #
    @1
    cc0
    wne
    #
    wa
    #
    @6
    cc
    wcel
    #
    @6
    cc0
    wne
    #
    wa
    #
    wa
    @31
    @16
    @13
    wa
    @15
    @32
    @12
    @33
    @0
    zcn
    @5
    zcn
    anim12i
    @16
    @36
    @13
    @39
    @16
    @34
    @35
    @1
    nncn
    @1
    nnne0
    jca
    @13
    @37
    @38
    @6
    nncn
    @6
    nnne0
    jca
    anim12i
    @0
    @5
    @1
    @6
    divadddiv
    syl2an
    an4s
    sylan9eqr
    @23
    @25
    @27
    w3a
    @10
    vu
    cv
    vv
    cv
    cdiv
    co
    wceq
    vv
    cn
    wrex
    vu
    cz
    wrex
    @11
    vu
    vv
    cz
    cn
    @22
    @24
    @10
    cdiv
    rspceov
    vu
    vv
    @10
    elq
    sylibr
    syl3anc
    an4s
    exp43
    rexlimivv
    rexlimdvv
    imp
    syl2anb
end
