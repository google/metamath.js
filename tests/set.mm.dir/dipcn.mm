include "cnv.mm"
include "wcel.mm"
include "cba.mm"
include "cfv.mm"
include "c1.mm"
include "c4.mm"
include "cfz.mm"
include "co.mm"
include "ci.mm"
include "cv.mm"
include "cexp.mm"
include "cns.mm"
include "cpv.mm"
include "cnmcv.mm"
include "c2.mm"
include "cmul.mm"
include "csu.mm"
include "cdiv.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "eqid.mm"
include "dipfval.mm"
include "cc.mm"
include "cxmt.mm"
include "ctopon.mm"
include "imsxmet.mm"
include "mopntopon.mm"
include "syl.mm"
include "fzfid.mm"
include "wa.mm"
include "adantr.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "cn0.mm"
include "ax-icn.mm"
include "cn.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnnn0d.mm"
include "expcl.mm"
include "sylancr.mm"
include "cnmpt2c.mm"
include "cnmpt1st.mm"
include "cnmpt2nd.mm"
include "smcn.mm"
include "cnmpt22f.mm"
include "vacn.mm"
include "nmcnc.mm"
include "cnmpt21f.mm"
include "cmpt.mm"
include "sqcn.mm"
include "oveq1.mm"
include "cnmpt21.mm"
include "mulcn.mm"
include "fsum2cn.mm"
include "cc0.mm"
include "wne.mm"
include "4cn.mm"
include "4ne0.mm"
include "divccn.mm"
include "mp2an.mm"
include "eqeltrd.mm"

theorem dipcn
  let cC: class C
  let cP: class P
  let cU: class U
  let cJ: class J
  let cK: class K
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dipcn.p: |- P = ( .iOLD ` U )
  assume dipcn.c: |- C = ( IndMet ` U )
  assume dipcn.j: |- J = ( MetOpen ` C )
  assume dipcn.k: |- K = ( TopOpen ` CCfld )


  assert |- ( U e. NrmCVec -> P e. ( ( J tX J ) Cn K ) )

  proof
    cU
    cnv
    wcel
    #
    cP
    vx
    vy
    cU
    cba
    cfv
    #
    @1
    c1
    c4
    cfz
    co
    #
    ci
    vk
    cv
    #
    cexp
    co
    #
    vx
    cv
    #
    @4
    vy
    cv
    #
    cU
    cns
    cfv
    #
    co
    #
    cU
    cpv
    cfv
    #
    co
    #
    cU
    cnmcv
    cfv
    #
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    c4
    cdiv
    co
    #
    cmpt2
    cJ
    cJ
    ctx
    co
    #
    cK
    ccn
    co
    vx
    vy
    cP
    @7
    cU
    vk
    @9
    @11
    @1
    @1
    eqid
    #
    @9
    eqid
    #
    @7
    eqid
    #
    @11
    eqid
    #
    dipcn.p
    dipfval
    @0
    vx
    vy
    vz
    @15
    vz
    cv
    #
    c4
    cdiv
    co
    #
    @16
    cJ
    cJ
    cK
    cK
    @1
    @1
    cc
    @0
    cC
    @1
    cxmt
    cfv
    wcel
    cJ
    @1
    ctopon
    cfv
    wcel
    #
    cC
    cU
    @1
    @18
    dipcn.c
    imsxmet
    cC
    cJ
    @1
    dipcn.j
    mopntopon
    syl
    #
    @25
    @0
    vx
    vy
    @2
    @14
    vk
    cJ
    cK
    cJ
    @1
    @1
    dipcn.k
    @25
    @0
    c1
    c4
    fzfid
    @25
    @0
    @3
    @2
    wcel
    #
    wa
    #
    vx
    vy
    @4
    @13
    cmul
    cJ
    cJ
    cK
    cK
    cK
    @1
    @1
    @0
    @24
    @26
    @25
    adantr
    #
    @28
    @27
    vx
    vy
    @4
    cJ
    cJ
    cK
    @1
    @1
    cc
    @28
    @28
    cK
    cc
    ctopon
    cfv
    wcel
    #
    @27
    cK
    dipcn.k
    cnfldtopon
    #
    a1i
    #
    @27
    ci
    cc
    wcel
    @3
    cn0
    wcel
    @4
    cc
    wcel
    ax-icn
    @27
    @3
    @26
    @3
    cn
    wcel
    @0
    @3
    c4
    elfznn
    adantl
    nnnn0d
    ci
    @3
    expcl
    sylancr
    cnmpt2c
    #
    @27
    vx
    vy
    vz
    @12
    @22
    c2
    cexp
    co
    #
    @13
    cJ
    cJ
    cK
    cK
    @1
    @1
    cc
    @28
    @28
    @27
    vx
    vy
    @10
    @11
    cJ
    cJ
    cJ
    cK
    @1
    @1
    @28
    @28
    @27
    vx
    vy
    @5
    @8
    @9
    cJ
    cJ
    cJ
    cJ
    cJ
    @1
    @1
    @28
    @28
    @27
    vx
    vy
    cJ
    cJ
    @1
    @1
    @28
    @28
    cnmpt1st
    @27
    vx
    vy
    @4
    @6
    @7
    cJ
    cJ
    cK
    cJ
    cJ
    @1
    @1
    @28
    @28
    @32
    @27
    vx
    vy
    cJ
    cJ
    @1
    @1
    @28
    @28
    cnmpt2nd
    @0
    @7
    cK
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    @26
    cC
    @7
    cU
    cJ
    cK
    dipcn.c
    dipcn.j
    @20
    dipcn.k
    smcn
    adantr
    cnmpt22f
    @0
    @9
    @17
    cJ
    ccn
    co
    wcel
    @26
    cC
    cU
    @9
    cJ
    dipcn.c
    dipcn.j
    @19
    vacn
    adantr
    cnmpt22f
    @0
    @11
    cJ
    cK
    ccn
    co
    wcel
    @26
    cC
    cU
    cJ
    cK
    @11
    @21
    dipcn.c
    dipcn.j
    dipcn.k
    nmcnc
    adantr
    cnmpt21f
    @31
    vz
    cc
    @33
    cmpt
    cK
    cK
    ccn
    co
    #
    wcel
    @27
    vz
    cK
    dipcn.k
    sqcn
    a1i
    @22
    @12
    c2
    cexp
    oveq1
    cnmpt21
    cmul
    cK
    cK
    ctx
    co
    cK
    ccn
    co
    wcel
    @27
    cK
    dipcn.k
    mulcn
    a1i
    cnmpt22f
    fsum2cn
    @29
    @0
    @30
    a1i
    vz
    cc
    @23
    cmpt
    @34
    wcel
    #
    @0
    c4
    cc
    wcel
    c4
    cc0
    wne
    @35
    4cn
    4ne0
    vz
    c4
    cK
    dipcn.k
    divccn
    mp2an
    a1i
    @22
    @15
    c4
    cdiv
    oveq1
    cnmpt21
    eqeltrd
end
