include "cn0.mm"
include "cc0.mm"
include "csn.mm"
include "wf.mm"
include "cxp.mm"
include "wceq.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "cun.mm"
include "cmap.mm"
include "co.mm"
include "wcel.mm"
include "cvv.mm"
include "wb.mm"
include "cc.mm"
include "0cnd.mm"
include "snssd.mm"
include "unssd.mm"
include "cnex.mm"
include "ssexg.mm"
include "sylancl.mm"
include "nn0ex.mm"
include "elmapg.mm"
include "mpbid.mm"
include "ffn.mm"
include "syl.mm"
include "cdm.mm"
include "cima.mm"
include "imadmrn.mm"
include "ccnv.mm"
include "fdm.mm"
include "fimacnv.mm"
include "eqtr4d.mm"
include "cdif.mm"
include "c0.mm"
include "simpr.mm"
include "wne.mm"
include "wa.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "adantr.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "c0p.mm"
include "cfz.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "eqid.mm"
include "plyeq0lem.mm"
include "pm2.21i.mm"
include "pm2.61dane.mm"
include "uneq1d.mm"
include "undif1.mm"
include "imaeq2i.mm"
include "imaundi.mm"
include "eqtr3i.mm"
include "un0.mm"
include "uncom.mm"
include "3eqtr4g.mm"
include "eqtrd.mm"
include "eqimss.mm"
include "wfun.mm"
include "ffun.mm"
include "ssid.mm"
include "funimass3.mm"
include "mpbird.mm"
include "syl5eqssr.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "c0ex.mm"
include "fconst2.mm"
include "sylib.mm"

theorem plyeq0
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cM: class M
  assume plyeq0.1: |- ( ph -> S C_ CC )
  assume plyeq0.2: |- ( ph -> N e. NN0 )
  assume plyeq0.3: |- ( ph -> A e. ( ( S u. { 0 } ) ^m NN0 ) )
  assume plyeq0.4: |- ( ph -> ( A " ( ZZ>= ` ( N + 1 ) ) ) = { 0 } )
  assume plyeq0.5: |- ( ph -> 0p = ( z e. CC |-> sum_ k e. ( 0 ... N ) ( ( A ` k ) x. ( z ^ k ) ) ) )

  disjoint k z
  disjoint A k
  disjoint A z
  disjoint N k
  disjoint N z
  disjoint k ph
  disjoint ph z
  disjoint S k
  disjoint S z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint x z
  disjoint A x
  disjoint M k
  disjoint M m
  disjoint M n
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint m ph
  disjoint n ph
  disjoint S x
  assert |- ( ph -> A = ( NN0 X. { 0 } ) )

  proof
    wph
    cn0
    cc0
    csn
    #
    cA
    wf
    #
    cA
    cn0
    @0
    cxp
    wceq
    wph
    cA
    cn0
    wfn
    #
    cA
    crn
    #
    @0
    wss
    @1
    wph
    cn0
    cS
    @0
    cun
    #
    cA
    wf
    #
    @2
    wph
    cA
    @4
    cn0
    cmap
    co
    wcel
    #
    @5
    plyeq0.3
    wph
    @4
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    @6
    @5
    wb
    wph
    @4
    cc
    wss
    cc
    cvv
    wcel
    @7
    wph
    cS
    @0
    cc
    plyeq0.1
    wph
    cc0
    cc
    wph
    0cnd
    snssd
    unssd
    cnex
    @4
    cc
    cvv
    ssexg
    sylancl
    nn0ex
    @4
    cn0
    cA
    cvv
    cvv
    elmapg
    sylancl
    mpbid
    #
    cn0
    @4
    cA
    ffn
    syl
    wph
    @3
    cA
    cA
    cdm
    #
    cima
    #
    @0
    cA
    imadmrn
    wph
    @10
    @0
    wss
    #
    @9
    cA
    ccnv
    #
    @0
    cima
    #
    wss
    #
    wph
    @9
    @13
    wceq
    @14
    wph
    @9
    @12
    @4
    cima
    #
    @13
    wph
    @5
    @9
    @15
    wceq
    @8
    @5
    @9
    cn0
    @15
    cn0
    @4
    cA
    fdm
    cn0
    @4
    cA
    fimacnv
    eqtr4d
    syl
    wph
    @12
    cS
    @0
    cdif
    #
    cima
    #
    @13
    cun
    #
    c0
    @13
    cun
    #
    @15
    @13
    wph
    @17
    c0
    @13
    wph
    @17
    c0
    wceq
    #
    @17
    c0
    wph
    @20
    simpr
    wph
    @17
    c0
    wne
    #
    wa
    #
    @20
    @22
    vz
    cA
    cS
    vk
    @17
    cr
    clt
    csup
    #
    cN
    wph
    cS
    cc
    wss
    @21
    plyeq0.1
    adantr
    wph
    cN
    cn0
    wcel
    @21
    plyeq0.2
    adantr
    wph
    @6
    @21
    plyeq0.3
    adantr
    wph
    cA
    cN
    c1
    caddc
    co
    cuz
    cfv
    cima
    @0
    wceq
    @21
    plyeq0.4
    adantr
    wph
    c0p
    vz
    cc
    cc0
    cN
    cfz
    co
    vk
    cv
    #
    cA
    cfv
    vz
    cv
    @24
    cexp
    co
    cmul
    co
    vk
    csu
    cmpt
    wceq
    @21
    plyeq0.5
    adantr
    @23
    eqid
    wph
    @21
    simpr
    plyeq0lem
    pm2.21i
    pm2.61dane
    uneq1d
    @12
    @16
    @0
    cun
    #
    cima
    @15
    @18
    @25
    @4
    @12
    cS
    @0
    undif1
    imaeq2i
    @12
    @16
    @0
    imaundi
    eqtr3i
    @13
    c0
    cun
    @13
    @19
    @13
    un0
    @13
    c0
    uncom
    eqtr3i
    3eqtr4g
    eqtrd
    @9
    @13
    eqimss
    syl
    wph
    cA
    wfun
    #
    @9
    @9
    wss
    @11
    @14
    wb
    wph
    @5
    @26
    @8
    cn0
    @4
    cA
    ffun
    syl
    @9
    ssid
    @9
    @0
    cA
    funimass3
    sylancl
    mpbird
    syl5eqssr
    cn0
    @0
    cA
    df-f
    sylanbrc
    cn0
    cc0
    cA
    c0ex
    fconst2
    sylib
end
