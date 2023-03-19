include "cq.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "cmul.mm"
include "elq.mm"
include "wa.mm"
include "wi.mm"
include "zmulcl.mm"
include "nnmulcl.mm"
include "anim12i.mm"
include "an4s.mm"
include "adantr.mm"
include "oveq12.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "zcn.mm"
include "ad2ant2r.mm"
include "nncn.mm"
include "nnne0.mm"
include "jca.mm"
include "ad2ant2l.mm"
include "divmuldiv.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "rspceov.mm"
include "3expa.mm"
include "sylibr.mm"
include "exp43.mm"
include "rexlimivv.mm"
include "rexlimdvv.mm"
include "imp.mm"
include "syl2anb.mm"

theorem qmulcl
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- ( ( A e. QQ /\ B e. QQ ) -> ( A x. B ) e. QQ )

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
    cmul
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
    @5
    cmul
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
    wa
    #
    @10
    @20
    @22
    cdiv
    co
    #
    wceq
    #
    @11
    @18
    @24
    @19
    @15
    @12
    @16
    @13
    @24
    @15
    @12
    wa
    @21
    @16
    @13
    wa
    @23
    @0
    @5
    zmulcl
    @1
    @6
    nnmulcl
    anim12i
    an4s
    adantr
    @19
    @18
    @10
    @2
    @7
    cmul
    co
    #
    @25
    cA
    @2
    cB
    @7
    cmul
    oveq12
    @18
    @0
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    wa
    #
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
    #
    @27
    @25
    wceq
    @15
    @12
    @30
    @16
    @13
    @15
    @28
    @12
    @29
    @0
    zcn
    @5
    zcn
    anim12i
    ad2ant2r
    @16
    @13
    @37
    @15
    @12
    @16
    @33
    @13
    @36
    @16
    @31
    @32
    @1
    nncn
    @1
    nnne0
    jca
    @13
    @34
    @35
    @6
    nncn
    @6
    nnne0
    jca
    anim12i
    ad2ant2l
    @0
    @5
    @1
    @6
    divmuldiv
    syl2anc
    sylan9eqr
    @24
    @26
    wa
    @10
    vv
    cv
    vu
    cv
    cdiv
    co
    wceq
    vu
    cn
    wrex
    vv
    cz
    wrex
    #
    @11
    @21
    @23
    @26
    @38
    vv
    vu
    cz
    cn
    @20
    @22
    @10
    cdiv
    rspceov
    3expa
    vv
    vu
    @10
    elq
    sylibr
    syl2anc
    an4s
    exp43
    rexlimivv
    rexlimdvv
    imp
    syl2anb
end
