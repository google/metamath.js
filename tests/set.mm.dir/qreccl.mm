include "cq.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cz.mm"
include "wi.mm"
include "elq.mm"
include "wa.mm"
include "cmul.mm"
include "nnne0.mm"
include "ancli.mm"
include "neeq1.mm"
include "cc.mm"
include "wb.mm"
include "zcn.mm"
include "nncn.mm"
include "anim12i.mm"
include "divne0b.mm"
include "3expa.mm"
include "sylan.mm"
include "bicomd.mm"
include "sylan9bbr.mm"
include "nnz.mm"
include "zmulcl.mm"
include "sylan2.mm"
include "adantr.mm"
include "msqznn.mm"
include "adantlr.mm"
include "jca.mm"
include "oveq2.mm"
include "divid.mm"
include "oveq1d.mm"
include "simpll.mm"
include "simpl.mm"
include "simpr.mm"
include "divdivdiv.mm"
include "syl22anc.mm"
include "eqtr3d.mm"
include "an4s.mm"
include "anass1rs.mm"
include "sylan9eqr.mm"
include "an32s.mm"
include "ex.mm"
include "sylbid.mm"
include "anasss.mm"
include "rspceov.mm"
include "sylibr.mm"
include "syl8.mm"
include "rexlimivv.mm"
include "sylbi.mm"
include "imp.mm"

theorem qreccl
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A e. QQ /\ A =/= 0 ) -> ( 1 / A ) e. QQ )

  proof
    cA
    cq
    wcel
    #
    cA
    cc0
    wne
    #
    c1
    cA
    cdiv
    co
    #
    cq
    wcel
    #
    @0
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
    @1
    @3
    wi
    #
    vx
    vy
    cA
    elq
    @7
    @8
    vx
    vy
    cz
    cn
    @4
    cz
    wcel
    #
    @5
    cn
    wcel
    #
    wa
    #
    @7
    @1
    @4
    @5
    cmul
    co
    #
    cz
    wcel
    #
    @4
    @4
    cmul
    co
    #
    cn
    wcel
    #
    wa
    #
    @2
    @12
    @14
    cdiv
    co
    #
    wceq
    #
    wa
    #
    @3
    @10
    @9
    @10
    @5
    cc0
    wne
    #
    wa
    @7
    @1
    @19
    wi
    #
    wi
    #
    @10
    @20
    @5
    nnne0
    ancli
    @9
    @10
    @20
    @22
    @11
    @20
    wa
    #
    @7
    @21
    @23
    @7
    wa
    #
    @1
    @4
    cc0
    wne
    #
    @19
    @7
    @1
    @6
    cc0
    wne
    #
    @23
    @25
    cA
    @6
    cc0
    neeq1
    @23
    @25
    @26
    @11
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    wa
    #
    @20
    @25
    @26
    wb
    #
    @9
    @27
    @10
    @28
    @4
    zcn
    @5
    nncn
    anim12i
    #
    @27
    @28
    @20
    @30
    @4
    @5
    divne0b
    3expa
    sylan
    bicomd
    sylan9bbr
    @24
    @25
    @19
    @24
    @25
    wa
    @16
    @18
    @23
    @25
    @16
    @7
    @11
    @25
    @16
    @20
    @11
    @25
    wa
    @13
    @15
    @11
    @13
    @25
    @10
    @9
    @5
    cz
    wcel
    @13
    @5
    nnz
    @4
    @5
    zmulcl
    sylan2
    adantr
    @9
    @25
    @15
    @10
    @4
    msqznn
    adantlr
    jca
    adantlr
    adantlr
    @23
    @25
    @7
    @18
    @7
    @23
    @25
    wa
    @2
    c1
    @6
    cdiv
    co
    #
    @17
    cA
    @6
    c1
    cdiv
    oveq2
    @11
    @25
    @20
    @32
    @17
    wceq
    #
    @11
    @29
    @25
    @20
    wa
    @33
    @31
    @27
    @25
    @28
    @20
    @33
    @27
    @25
    wa
    #
    @28
    @20
    wa
    #
    wa
    #
    @4
    @4
    cdiv
    co
    #
    @6
    cdiv
    co
    #
    @32
    @17
    @36
    @37
    c1
    @6
    cdiv
    @34
    @37
    c1
    wceq
    @35
    @4
    divid
    adantr
    oveq1d
    @36
    @27
    @34
    @34
    @35
    @38
    @17
    wceq
    @27
    @25
    @35
    simpll
    @34
    @35
    simpl
    #
    @39
    @34
    @35
    simpr
    @4
    @4
    @4
    @5
    divdivdiv
    syl22anc
    eqtr3d
    an4s
    sylan
    anass1rs
    sylan9eqr
    an32s
    jca
    ex
    sylbid
    ex
    anasss
    sylan2
    @19
    @2
    vz
    cv
    vw
    cv
    cdiv
    co
    wceq
    vw
    cn
    wrex
    vz
    cz
    wrex
    #
    @3
    @13
    @15
    @18
    @40
    vz
    vw
    cz
    cn
    @12
    @14
    @2
    cdiv
    rspceov
    3expa
    vz
    vw
    @2
    elq
    sylibr
    syl8
    rexlimivv
    sylbi
    imp
end
