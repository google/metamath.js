include "climc.mm"
include "co.mm"
include "cc.mm"
include "cv.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "cin.mm"
include "cima.mm"
include "wss.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "ellimc2.mm"
include "ccl.mm"
include "cfv.mm"
include "ccld.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "adantr.mm"
include "ssdifssd.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "clscld.mm"
include "sylancr.mm"
include "cldopn.mm"
include "syl.mm"
include "clp.mm"
include "wb.mm"
include "islp.mm"
include "mtbid.mm"
include "eldifd.mm"
include "c0.mm"
include "wceq.mm"
include "difin2.mm"
include "sscls.mm"
include "ssdif0.mm"
include "sylib.mm"
include "eqtr3d.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "syl6eq.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "eleq2.mm"
include "ineq1.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "a1d.mm"
include "ralrimivw.mm"
include "ex.mm"
include "pm4.71d.mm"
include "bitr4d.mm"
include "eqrdv.mm"

theorem limcnlp
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cK: class K
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cC: class C
  assume limccl.f: |- ( ph -> F : A --> CC )
  assume limccl.a: |- ( ph -> A C_ CC )
  assume limccl.b: |- ( ph -> B e. CC )
  assume ellimc2.k: |- K = ( TopOpen ` CCfld )
  assume limcnlp.n: |- ( ph -> -. B e. ( ( limPt ` K ) ` A ) )


  assert |- ( ph -> ( F limCC B ) = CC )

  proof
    wph
    vx
    cF
    cB
    climc
    co
    #
    cc
    wph
    vx
    cv
    #
    @0
    wcel
    @1
    cc
    wcel
    #
    @1
    vu
    cv
    #
    wcel
    #
    cB
    vv
    cv
    #
    wcel
    #
    cF
    @5
    cA
    cB
    csn
    #
    cdif
    #
    cin
    #
    cima
    #
    @3
    wss
    #
    wa
    #
    vv
    cK
    wrex
    #
    wi
    #
    vu
    cK
    wral
    #
    wa
    @2
    wph
    vv
    vu
    cA
    cB
    @1
    cF
    cK
    limccl.f
    limccl.a
    limccl.b
    ellimc2.k
    ellimc2
    wph
    @2
    @15
    wph
    @2
    @15
    wph
    @2
    wa
    #
    @14
    vu
    cK
    @16
    @13
    @4
    @16
    cc
    @8
    cK
    ccl
    cfv
    cfv
    #
    cdif
    #
    cK
    wcel
    #
    cB
    @18
    wcel
    #
    cF
    @18
    @8
    cin
    #
    cima
    #
    @3
    wss
    #
    @13
    @16
    @17
    cK
    ccld
    cfv
    wcel
    #
    @19
    @16
    cK
    ctop
    wcel
    #
    @8
    cc
    wss
    #
    @24
    cK
    ellimc2.k
    cnfldtop
    #
    @16
    cA
    cc
    @7
    wph
    cA
    cc
    wss
    #
    @2
    limccl.a
    adantr
    ssdifssd
    #
    @8
    cK
    cc
    cc
    cK
    cK
    ellimc2.k
    cnfldtopon
    toponunii
    #
    clscld
    sylancr
    @17
    cK
    cc
    @30
    cldopn
    syl
    wph
    @20
    @2
    wph
    cB
    cc
    @17
    limccl.b
    wph
    cB
    cA
    cK
    clp
    cfv
    cfv
    wcel
    #
    cB
    @17
    wcel
    #
    limcnlp.n
    wph
    @25
    @28
    @31
    @32
    wb
    @27
    limccl.a
    cB
    cA
    cK
    cc
    @30
    islp
    sylancr
    mtbid
    eldifd
    adantr
    @16
    @22
    c0
    @3
    @16
    @22
    cF
    c0
    cima
    c0
    @16
    @21
    c0
    cF
    @16
    @8
    @17
    cdif
    #
    @21
    c0
    @16
    @26
    @33
    @21
    wceq
    @29
    @8
    @17
    cc
    difin2
    syl
    @16
    @8
    @17
    wss
    #
    @33
    c0
    wceq
    @16
    @25
    @26
    @34
    @27
    @29
    @8
    cK
    cc
    @30
    sscls
    sylancr
    @8
    @17
    ssdif0
    sylib
    eqtr3d
    imaeq2d
    cF
    ima0
    syl6eq
    @3
    0ss
    syl6eqss
    @12
    @20
    @23
    wa
    vv
    @18
    cK
    @5
    @18
    wceq
    #
    @6
    @20
    @11
    @23
    @5
    @18
    cB
    eleq2
    @35
    @10
    @22
    @3
    @35
    @9
    @21
    cF
    @5
    @18
    @8
    ineq1
    imaeq2d
    sseq1d
    anbi12d
    rspcev
    syl12anc
    a1d
    ralrimivw
    ex
    pm4.71d
    bitr4d
    eqrdv
end
