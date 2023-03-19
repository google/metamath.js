include "cv.mm"
include "cdif.mm"
include "wcel.mm"
include "csu.mm"
include "clt.mm"
include "wbr.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "wex.mm"
include "cfn.mm"
include "cz.mm"
include "uzinf.mm"
include "syl.mm"
include "wss.mm"
include "ssdif0.mm"
include "wa.mm"
include "eqss.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "syl5bir.mm"
include "mpand.mm"
include "mtod.mm"
include "neq0.mm"
include "sylib.mm"
include "csn.mm"
include "cun.mm"
include "adantr.mm"
include "cr.mm"
include "sselda.mm"
include "crp.mm"
include "adantlr.mm"
include "rpred.mm"
include "syldan.mm"
include "fsumrecl.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "eldifi.mm"
include "snssd.mm"
include "anim12i.mm"
include "unss.mm"
include "cfv.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "isumrecl.mm"
include "co.mm"
include "a1i.mm"
include "wne.mm"
include "vex.mm"
include "snnz.mm"
include "adantl.mm"
include "fsumrpcl.mm"
include "ltaddrpd.mm"
include "cin.mm"
include "eldifn.mm"
include "disjsn.mm"
include "sylibr.mm"
include "eqidd.mm"
include "cc.mm"
include "rpcnd.mm"
include "fsumsplit.mm"
include "breqtrrd.mm"
include "rpge0d.mm"
include "isumless.mm"
include "ltletrd.mm"
include "exlimddv.mm"

theorem isumltss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vx: setvar x
  assume isumltss.1: |- Z = ( ZZ>= ` M )
  assume isumltss.2: |- ( ph -> M e. ZZ )
  assume isumltss.3: |- ( ph -> A e. Fin )
  assume isumltss.4: |- ( ph -> A C_ Z )
  assume isumltss.5: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume isumltss.6: |- ( ( ph /\ k e. Z ) -> B e. RR+ )
  assume isumltss.7: |- ( ph -> seq M ( + , F ) e. dom ~~> )

  disjoint A k
  disjoint F k
  disjoint M k
  disjoint k ph
  disjoint Z k
  disjoint k x
  disjoint A x
  disjoint B x
  disjoint M x
  disjoint ph x
  disjoint Z x
  assert |- ( ph -> sum_ k e. A B < sum_ k e. Z B )

  proof
    wph
    vx
    cv
    #
    cZ
    cA
    cdif
    #
    wcel
    #
    cA
    cB
    vk
    csu
    #
    cZ
    cB
    vk
    csu
    #
    clt
    wbr
    vx
    wph
    @1
    c0
    wceq
    #
    wn
    @2
    vx
    wex
    wph
    @5
    cZ
    cfn
    wcel
    #
    wph
    cM
    cz
    wcel
    #
    @6
    wn
    isumltss.2
    cM
    cZ
    isumltss.1
    uzinf
    syl
    @5
    cZ
    cA
    wss
    #
    wph
    @6
    cZ
    cA
    ssdif0
    wph
    cA
    cZ
    wss
    #
    @8
    @6
    isumltss.4
    @9
    @8
    wa
    cA
    cZ
    wceq
    #
    wph
    @6
    cA
    cZ
    eqss
    wph
    cA
    cfn
    wcel
    #
    @10
    @6
    isumltss.3
    cA
    cZ
    cfn
    eleq1
    syl5ibcom
    syl5bir
    mpand
    syl5bir
    mtod
    vx
    @1
    neq0
    sylib
    wph
    @2
    wa
    #
    @3
    cA
    @0
    csn
    #
    cun
    #
    cB
    vk
    csu
    #
    @4
    @12
    cA
    cB
    vk
    wph
    @11
    @2
    isumltss.3
    adantr
    #
    @12
    vk
    cv
    #
    cA
    wcel
    @17
    cZ
    wcel
    #
    cB
    cr
    wcel
    #
    @12
    cA
    cZ
    @17
    wph
    @9
    @2
    isumltss.4
    adantr
    sselda
    @12
    @18
    wa
    #
    cB
    wph
    @18
    cB
    crp
    wcel
    #
    @2
    isumltss.6
    adantlr
    #
    rpred
    #
    syldan
    fsumrecl
    #
    @12
    @14
    cB
    vk
    @12
    @11
    @13
    cfn
    wcel
    #
    @14
    cfn
    wcel
    @16
    @0
    snfi
    #
    cA
    @13
    unfi
    sylancl
    #
    @12
    @17
    @14
    wcel
    #
    @18
    @19
    @12
    @14
    cZ
    @17
    @12
    @9
    @13
    cZ
    wss
    #
    wa
    @14
    cZ
    wss
    wph
    @9
    @2
    @29
    isumltss.4
    @2
    @0
    cZ
    @0
    cZ
    cA
    eldifi
    snssd
    #
    anim12i
    cA
    @13
    cZ
    unss
    sylib
    #
    sselda
    #
    @23
    syldan
    fsumrecl
    @12
    cB
    vk
    cF
    cM
    cZ
    isumltss.1
    wph
    @7
    @2
    isumltss.2
    adantr
    #
    wph
    @18
    @17
    cF
    cfv
    cB
    wceq
    @2
    isumltss.5
    adantlr
    #
    @23
    wph
    caddc
    cF
    cM
    cseq
    cli
    cdm
    wcel
    @2
    isumltss.7
    adantr
    #
    isumrecl
    @12
    @3
    @3
    @13
    cB
    vk
    csu
    #
    caddc
    co
    @15
    clt
    @12
    @3
    @36
    @24
    @12
    @13
    cB
    vk
    @25
    @12
    @26
    a1i
    @13
    c0
    wne
    @12
    @0
    vx
    vex
    snnz
    a1i
    @12
    @17
    @13
    wcel
    @18
    @21
    @12
    @13
    cZ
    @17
    @2
    @29
    wph
    @30
    adantl
    sselda
    @22
    syldan
    fsumrpcl
    ltaddrpd
    @12
    cA
    @13
    cB
    @14
    vk
    @12
    @0
    cA
    wcel
    wn
    #
    cA
    @13
    cin
    c0
    wceq
    @2
    @37
    wph
    @0
    cZ
    cA
    eldifn
    adantl
    cA
    @0
    disjsn
    sylibr
    @12
    @14
    eqidd
    @27
    @12
    @28
    @18
    cB
    cc
    wcel
    @32
    @20
    cB
    @22
    rpcnd
    syldan
    fsumsplit
    breqtrrd
    @12
    @14
    cB
    vk
    cF
    cM
    cZ
    isumltss.1
    @33
    @27
    @31
    @34
    @23
    @20
    cB
    @22
    rpge0d
    @35
    isumless
    ltletrd
    exlimddv
end
