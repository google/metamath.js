include "climc.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "caddc.mm"
include "cuz.mm"
include "cv.mm"
include "cmpt.mm"
include "clsp.mm"
include "wcel.mm"
include "crp.mm"
include "cioo.mm"
include "cr.mm"
include "cdv.mm"
include "cabs.mm"
include "crn.mm"
include "csup.mm"
include "c2.mm"
include "cle.mm"
include "cif.mm"
include "adantr.mm"
include "simpr.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "supeq1i.mm"
include "eqid.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "biid.mm"
include "ioodvbdlimc2lem.mm"
include "ne0i.mm"
include "syl.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "fssd.mm"
include "cxr.mm"
include "wb.mm"
include "rexrd.mm"
include "ioo0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "feq2d.mm"
include "mpbid.mm"
include "recnd.mm"
include "limcdm0.mm"
include "cc0.mm"
include "0cn.mm"
include "ne0ii.mm"
include "eqnetrd.mm"
include "ltlecasei.mm"

theorem ioodvbdlimc2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  assume ioodvbdlimc2.a: |- ( ph -> A e. RR )
  assume ioodvbdlimc2.b: |- ( ph -> B e. RR )
  assume ioodvbdlimc2.f: |- ( ph -> F : ( A (,) B ) --> RR )
  assume ioodvbdlimc2.dmdv: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume ioodvbdlimc2.dvbd: |- ( ph -> E. y e. RR A. x e. ( A (,) B ) ( abs ` ( ( RR _D F ) ` x ) ) <_ y )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint ph x
  disjoint ph y
  disjoint A j
  disjoint A k
  disjoint A z
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x z
  disjoint y z
  disjoint B j
  disjoint B k
  disjoint B z
  disjoint F j
  disjoint F k
  disjoint F z
  disjoint j ph
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( F limCC B ) =/= (/) )

  proof
    wph
    cF
    cB
    climc
    co
    #
    c0
    wne
    #
    cA
    cB
    wph
    cA
    cB
    clt
    wbr
    #
    wa
    #
    vk
    c1
    cB
    cA
    cmin
    co
    cdiv
    co
    cfl
    cfv
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cB
    c1
    vk
    cv
    #
    cdiv
    co
    #
    cmin
    co
    #
    cF
    cfv
    #
    cmpt
    #
    clsp
    cfv
    #
    @0
    wcel
    @1
    @3
    @3
    vx
    cv
    #
    crp
    wcel
    wa
    vj
    cv
    #
    @4
    vy
    cA
    cB
    cioo
    co
    #
    vy
    cv
    #
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cabs
    cfv
    #
    cmpt
    #
    crn
    #
    cr
    clt
    csup
    #
    @12
    c2
    cdiv
    co
    #
    cdiv
    co
    cfl
    cfv
    c1
    caddc
    co
    #
    cle
    wbr
    @23
    @4
    cif
    #
    cuz
    cfv
    wcel
    wa
    @13
    @10
    cfv
    @11
    cmin
    co
    cabs
    cfv
    @22
    clt
    wbr
    wa
    vz
    cv
    #
    @14
    wcel
    wa
    @25
    cB
    cmin
    co
    cabs
    cfv
    c1
    @13
    cdiv
    co
    #
    clt
    wbr
    wa
    #
    vx
    vy
    vz
    cA
    cB
    vk
    @5
    @8
    cmpt
    @10
    vj
    cF
    @4
    @24
    @21
    wph
    cA
    cr
    wcel
    @2
    ioodvbdlimc2.a
    adantr
    wph
    cB
    cr
    wcel
    @2
    ioodvbdlimc2.b
    adantr
    wph
    @2
    simpr
    wph
    @14
    cr
    cF
    wf
    @2
    ioodvbdlimc2.f
    adantr
    wph
    @16
    cdm
    @14
    wceq
    @2
    ioodvbdlimc2.dmdv
    adantr
    wph
    @12
    @16
    cfv
    #
    cabs
    cfv
    #
    @15
    cle
    wbr
    vx
    @14
    wral
    vy
    cr
    wrex
    @2
    ioodvbdlimc2.dvbd
    adantr
    cr
    @20
    vx
    @14
    @29
    cmpt
    #
    crn
    clt
    @19
    @30
    vy
    vx
    @14
    @18
    @29
    @15
    @12
    wceq
    @17
    @28
    cabs
    @15
    @12
    @16
    fveq2
    fveq2d
    cbvmptv
    rneqi
    supeq1i
    @4
    eqid
    vk
    vj
    @5
    @9
    cB
    @26
    cmin
    co
    #
    cF
    cfv
    @6
    @13
    wceq
    #
    @8
    @31
    cF
    @32
    @7
    @26
    cB
    cmin
    @6
    @13
    c1
    cdiv
    oveq2
    oveq2d
    #
    fveq2d
    cbvmptv
    vk
    vj
    @5
    @8
    @31
    @33
    cbvmptv
    @24
    eqid
    @27
    biid
    ioodvbdlimc2lem
    @0
    @11
    ne0i
    syl
    wph
    cB
    cA
    cle
    wbr
    #
    wa
    #
    @0
    cc
    c0
    @35
    cB
    cF
    @35
    @14
    cc
    cF
    wf
    #
    c0
    cc
    cF
    wf
    wph
    @36
    @34
    wph
    @14
    cr
    cc
    cF
    ioodvbdlimc2.f
    cr
    cc
    wss
    wph
    ax-resscn
    a1i
    fssd
    adantr
    @35
    @14
    c0
    cc
    cF
    @35
    @14
    c0
    wceq
    #
    @34
    wph
    @34
    simpr
    @35
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @37
    @34
    wb
    wph
    @38
    @34
    wph
    cA
    ioodvbdlimc2.a
    rexrd
    adantr
    wph
    @39
    @34
    wph
    cB
    ioodvbdlimc2.b
    rexrd
    adantr
    cA
    cB
    ioo0
    syl2anc
    mpbird
    feq2d
    mpbid
    wph
    cB
    cc
    wcel
    @34
    wph
    cB
    ioodvbdlimc2.b
    recnd
    adantr
    limcdm0
    cc
    c0
    wne
    @35
    cc0
    cc
    0cn
    ne0ii
    a1i
    eqnetrd
    ioodvbdlimc2.a
    ioodvbdlimc2.b
    ltlecasei
end
