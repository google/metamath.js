include "cv.mm"
include "cprod.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "prodeq1.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "c1.mm"
include "abs1.mm"
include "prod0.mm"
include "fveq2i.mm"
include "3eqtr4i.mm"
include "a1i.mm"
include "wss.mm"
include "cdif.mm"
include "wcel.mm"
include "wa.mm"
include "csb.mm"
include "cmul.mm"
include "co.mm"
include "eqidd.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "cfn.mm"
include "adantr.mm"
include "simpr.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "adantrr.mm"
include "simprr.mm"
include "eldifbd.mm"
include "cc.mm"
include "simpll.mm"
include "sselda.mm"
include "adantlrr.mm"
include "csbeq1a.mm"
include "simpl.mm"
include "eldifad.mm"
include "wi.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "fprodsplitsn.mm"
include "fprodclf.mm"
include "absmuld.mm"
include "oveq1.mm"
include "adantl.mm"
include "3eqtrd.mm"
include "nfcv.mm"
include "nffv.mm"
include "abscld.mm"
include "recnd.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "findcard2d.mm"

theorem fprodabs2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fprodabs2.a: |- ( ph -> A e. Fin )
  assume fprodabs2.b: |- ( ( ph /\ k e. A ) -> B e. CC )

  disjoint A k
  disjoint k ph
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( abs ` prod_ k e. A B ) = prod_ k e. A ( abs ` B ) )

  proof
    wph
    vx
    cv
    #
    cB
    vk
    cprod
    #
    cabs
    cfv
    #
    @0
    cB
    cabs
    cfv
    #
    vk
    cprod
    #
    wceq
    c0
    cB
    vk
    cprod
    #
    cabs
    cfv
    #
    c0
    @3
    vk
    cprod
    #
    wceq
    #
    vy
    cv
    #
    cB
    vk
    cprod
    #
    cabs
    cfv
    #
    @9
    @3
    vk
    cprod
    #
    wceq
    #
    @9
    vz
    cv
    #
    csn
    cun
    #
    cB
    vk
    cprod
    #
    cabs
    cfv
    #
    @15
    @3
    vk
    cprod
    #
    wceq
    #
    cA
    cB
    vk
    cprod
    #
    cabs
    cfv
    #
    cA
    @3
    vk
    cprod
    #
    wceq
    vx
    vy
    vz
    cA
    @0
    c0
    wceq
    #
    @2
    @6
    @4
    @7
    @23
    @1
    @5
    cabs
    @0
    c0
    cB
    vk
    prodeq1
    fveq2d
    @0
    c0
    @3
    vk
    prodeq1
    eqeq12d
    @0
    @9
    wceq
    #
    @2
    @11
    @4
    @12
    @24
    @1
    @10
    cabs
    @0
    @9
    cB
    vk
    prodeq1
    fveq2d
    @0
    @9
    @3
    vk
    prodeq1
    eqeq12d
    @0
    @15
    wceq
    #
    @2
    @17
    @4
    @18
    @25
    @1
    @16
    cabs
    @0
    @15
    cB
    vk
    prodeq1
    fveq2d
    @0
    @15
    @3
    vk
    prodeq1
    eqeq12d
    @0
    cA
    wceq
    #
    @2
    @21
    @4
    @22
    @26
    @1
    @20
    cabs
    @0
    cA
    cB
    vk
    prodeq1
    fveq2d
    @0
    cA
    @3
    vk
    prodeq1
    eqeq12d
    @8
    wph
    c1
    cabs
    cfv
    c1
    @6
    @7
    abs1
    @5
    c1
    cabs
    cB
    vk
    prod0
    fveq2i
    @3
    vk
    prod0
    3eqtr4i
    a1i
    wph
    @9
    cA
    wss
    #
    @14
    cA
    @9
    cdif
    #
    wcel
    #
    wa
    #
    wa
    #
    @13
    @19
    @31
    @13
    wa
    #
    @12
    vk
    @14
    cB
    csb
    #
    cabs
    cfv
    #
    cmul
    co
    #
    @35
    @17
    @18
    @32
    @35
    eqidd
    @32
    @17
    @10
    @33
    cmul
    co
    #
    cabs
    cfv
    #
    @11
    @34
    cmul
    co
    #
    @35
    @32
    @16
    @36
    cabs
    @31
    @16
    @36
    wceq
    @13
    @31
    @9
    @14
    cB
    @33
    vk
    @28
    @31
    vk
    nfv
    #
    vk
    @14
    cB
    nfcsb1v
    #
    wph
    @27
    @9
    cfn
    wcel
    #
    @29
    wph
    @27
    wa
    #
    cA
    cfn
    wcel
    #
    @27
    @41
    wph
    @43
    @27
    fprodabs2.a
    adantr
    wph
    @27
    simpr
    #
    cA
    @9
    ssfi
    syl2anc
    adantrr
    #
    wph
    @27
    @29
    simprr
    #
    @31
    @14
    cA
    @9
    @46
    eldifbd
    #
    @31
    vk
    cv
    #
    @9
    wcel
    #
    wa
    #
    wph
    @48
    cA
    wcel
    #
    cB
    cc
    wcel
    #
    wph
    @30
    @49
    simpll
    wph
    @27
    @49
    @51
    @29
    @42
    @9
    cA
    @48
    @44
    sselda
    adantlrr
    fprodabs2.b
    syl2anc
    #
    vk
    @14
    cB
    csbeq1a
    #
    @31
    wph
    @14
    cA
    wcel
    #
    @33
    cc
    wcel
    #
    wph
    @30
    simpl
    @31
    @14
    cA
    @9
    @46
    eldifad
    wph
    @51
    wa
    #
    @52
    wi
    wph
    @55
    wa
    #
    @56
    wi
    vk
    vz
    @58
    @56
    vk
    @58
    vk
    nfv
    vk
    @33
    cc
    @40
    nfel1
    nfim
    @48
    @14
    wceq
    #
    @57
    @58
    @52
    @56
    @59
    @51
    @55
    wph
    @48
    @14
    cA
    eleq1
    anbi2d
    @59
    cB
    @33
    cc
    @54
    eleq1d
    imbi12d
    fprodabs2.b
    chvar
    syl2anc
    #
    fprodsplitsn
    adantr
    fveq2d
    @31
    @37
    @38
    wceq
    @13
    @31
    @10
    @33
    @31
    @9
    cB
    vk
    @39
    @45
    @53
    fprodclf
    @60
    absmuld
    adantr
    @13
    @38
    @35
    wceq
    @31
    @11
    @12
    @34
    cmul
    oveq1
    adantl
    3eqtrd
    @31
    @18
    @35
    wceq
    @13
    @31
    @9
    @14
    @3
    @34
    vk
    @28
    @39
    vk
    @33
    cabs
    vk
    cabs
    nfcv
    @40
    nffv
    @45
    @46
    @47
    @50
    @3
    @50
    cB
    @53
    abscld
    recnd
    @59
    cB
    @33
    cabs
    @54
    fveq2d
    @31
    @34
    @31
    @33
    @60
    abscld
    recnd
    fprodsplitsn
    adantr
    3eqtr4d
    ex
    fprodabs2.a
    findcard2d
end
