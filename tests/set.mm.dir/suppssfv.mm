include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cmpt.mm"
include "csupp.mm"
include "co.mm"
include "wss.mm"
include "wi.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wne.mm"
include "cv.mm"
include "eldifsni.mm"
include "elex.mm"
include "syl.mm"
include "adantll.mm"
include "adantr.mm"
include "wceq.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "necon3d.mm"
include "adantl.mm"
include "imp.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "ex.mm"
include "syl5.mm"
include "ss2rabdv.mm"
include "eqid.mm"
include "simpll.mm"
include "simplr.mm"
include "mptsuppdifd.mm"
include "3sstr4d.mm"
include "sstrd.mm"
include "wn.mm"
include "c0.mm"
include "mptexg.mm"
include "cdm.mm"
include "wral.mm"
include "fvex.mm"
include "rgenw.mm"
include "dmmptg.mm"
include "ax-mp.mm"
include "dmexg.mm"
include "syl5eqelr.mm"
include "impbii.mm"
include "anbi1i.mm"
include "supp0prc.mm"
include "sylnbi.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem suppssfv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cU: class U
  let cF: class F
  let cL: class L
  let cV: class V
  let cY: class Y
  let cZ: class Z
  assume suppssfv.a: |- ( ph -> ( ( x e. D |-> A ) supp Y ) C_ L )
  assume suppssfv.f: |- ( ph -> ( F ` Y ) = Z )
  assume suppssfv.v: |- ( ( ph /\ x e. D ) -> A e. V )
  assume suppssfv.y: |- ( ph -> Y e. U )

  disjoint ph x
  disjoint D x
  disjoint Y x
  disjoint Z x
  assert |- ( ph -> ( ( x e. D |-> ( F ` A ) ) supp Z ) C_ L )

  proof
    cD
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    wa
    #
    wph
    vx
    cD
    cA
    cF
    cfv
    #
    cmpt
    #
    cZ
    csupp
    co
    #
    cL
    wss
    #
    wi
    @2
    wph
    @6
    @2
    wph
    wa
    #
    @5
    vx
    cD
    cA
    cmpt
    #
    cY
    csupp
    co
    #
    cL
    @7
    @3
    cvv
    cZ
    csn
    cdif
    wcel
    #
    vx
    cD
    crab
    cA
    cvv
    cY
    csn
    cdif
    wcel
    #
    vx
    cD
    crab
    @5
    @9
    @7
    @10
    @11
    vx
    cD
    @10
    @3
    cZ
    wne
    #
    @7
    vx
    cv
    cD
    wcel
    #
    wa
    #
    @11
    @3
    cvv
    cZ
    eldifsni
    @14
    @12
    @11
    @14
    @12
    wa
    cA
    cvv
    wcel
    #
    cA
    cY
    wne
    #
    @11
    @14
    @15
    @12
    wph
    @13
    @15
    @2
    wph
    @13
    wa
    cA
    cV
    wcel
    @15
    suppssfv.v
    cA
    cV
    elex
    syl
    adantll
    adantr
    @14
    @12
    @16
    @7
    @12
    @16
    wi
    #
    @13
    wph
    @17
    @2
    wph
    cA
    cY
    @3
    cZ
    wph
    @3
    cZ
    wceq
    cA
    cY
    wceq
    #
    cY
    cF
    cfv
    #
    cZ
    wceq
    suppssfv.f
    @18
    @3
    @19
    cZ
    cA
    cY
    cF
    fveq2
    eqeq1d
    syl5ibrcom
    necon3d
    adantl
    adantr
    imp
    cA
    cvv
    cY
    eldifsn
    sylanbrc
    ex
    syl5
    ss2rabdv
    @7
    vx
    cD
    @3
    @4
    cvv
    cvv
    cZ
    @4
    eqid
    @0
    @1
    wph
    simpll
    #
    @0
    @1
    wph
    simplr
    mptsuppdifd
    @7
    vx
    cD
    cA
    @8
    cvv
    cU
    cY
    @8
    eqid
    @20
    wph
    cY
    cU
    wcel
    @2
    suppssfv.y
    adantl
    mptsuppdifd
    3sstr4d
    wph
    @9
    cL
    wss
    @2
    suppssfv.a
    adantl
    sstrd
    ex
    @2
    wn
    #
    @6
    wph
    @21
    @5
    c0
    cL
    @2
    @4
    cvv
    wcel
    #
    @1
    wa
    @5
    c0
    wceq
    @0
    @22
    @1
    @0
    @22
    vx
    cD
    @3
    cvv
    mptexg
    @22
    cD
    @4
    cdm
    #
    cvv
    @3
    cvv
    wcel
    #
    vx
    cD
    wral
    @23
    cD
    wceq
    @24
    vx
    cD
    cA
    cF
    fvex
    rgenw
    vx
    cD
    @3
    cvv
    dmmptg
    ax-mp
    @4
    cvv
    dmexg
    syl5eqelr
    impbii
    anbi1i
    @4
    cZ
    supp0prc
    sylnbi
    cL
    0ss
    syl6eqss
    a1d
    pm2.61i
end
