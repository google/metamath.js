include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cnsb.mm"
include "cfv.mm"
include "wi.mm"
include "cnv.mm"
include "phnvi.mm"
include "eqid.mm"
include "nvmcl.mm"
include "mp3an1.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "rspcv.mm"
include "syl.mm"
include "cmin.mm"
include "cc0.mm"
include "cn0v.mm"
include "simpl.mm"
include "simpr.mm"
include "ccphlo.mm"
include "w3a.mm"
include "dipsubdi.mm"
include "mpan.mm"
include "syl3anc.mm"
include "eqeq1d.mm"
include "wb.mm"
include "ipz.mm"
include "bitr3d.mm"
include "cc.mm"
include "dipcl.mm"
include "syl2anc.mm"
include "sylancom.mm"
include "subeq0ad.mm"
include "nvmeq0.mm"
include "3bitr3d.mm"
include "sylibd.mm"
include "oveq2.mm"
include "ralrimivw.mm"
include "impbid1.mm"

theorem ip2eqi
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let cX: class X
  let vs: setvar s
  let vt: setvar t
  let cQ: class Q
  let vy: setvar y
  let cS: class S
  let cT: class T
  let cY: class Y
  assume ip2eqi.1: |- X = ( BaseSet ` U )
  assume ip2eqi.7: |- P = ( .iOLD ` U )
  assume ip2eqi.u: |- U e. CPreHilOLD

  disjoint A x
  disjoint B x
  disjoint P x
  disjoint U x
  disjoint X x
  disjoint s t
  disjoint s x
  disjoint P s
  disjoint t x
  disjoint P t
  disjoint Q s
  disjoint Q t
  disjoint x y
  disjoint S x
  disjoint S y
  disjoint s y
  disjoint T s
  disjoint t y
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint X s
  disjoint X t
  disjoint X y
  disjoint Y s
  disjoint Y t
  disjoint Y x
  disjoint Y y
  assert |- ( ( A e. X /\ B e. X ) -> ( A. x e. X ( x P A ) = ( x P B ) <-> A = B ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    wa
    #
    vx
    cv
    #
    cA
    cP
    co
    #
    @3
    cB
    cP
    co
    #
    wceq
    #
    vx
    cX
    wral
    #
    cA
    cB
    wceq
    #
    @2
    @7
    cA
    cB
    cU
    cnsb
    cfv
    #
    co
    #
    cA
    cP
    co
    #
    @10
    cB
    cP
    co
    #
    wceq
    #
    @8
    @2
    @10
    cX
    wcel
    #
    @7
    @13
    wi
    cU
    cnv
    wcel
    #
    @0
    @1
    @14
    cU
    ip2eqi.u
    phnvi
    #
    cA
    cB
    cU
    @9
    cX
    ip2eqi.1
    @9
    eqid
    #
    nvmcl
    mp3an1
    #
    @6
    @13
    vx
    @10
    cX
    @3
    @10
    wceq
    @4
    @11
    @5
    @12
    @3
    @10
    cA
    cP
    oveq1
    @3
    @10
    cB
    cP
    oveq1
    eqeq12d
    rspcv
    syl
    @2
    @11
    @12
    cmin
    co
    #
    cc0
    wceq
    #
    @10
    cU
    cn0v
    cfv
    #
    wceq
    #
    @13
    @8
    @2
    @10
    @10
    cP
    co
    #
    cc0
    wceq
    #
    @20
    @22
    @2
    @23
    @19
    cc0
    @2
    @14
    @0
    @1
    @23
    @19
    wceq
    #
    @18
    @0
    @1
    simpl
    #
    @0
    @1
    simpr
    cU
    ccphlo
    wcel
    @14
    @0
    @1
    w3a
    @25
    ip2eqi.u
    @10
    cA
    cB
    cP
    cU
    @9
    cX
    ip2eqi.1
    @17
    ip2eqi.7
    dipsubdi
    mpan
    syl3anc
    eqeq1d
    @2
    @14
    @24
    @22
    wb
    #
    @18
    @15
    @14
    @27
    @16
    @10
    cP
    cU
    cX
    @21
    ip2eqi.1
    @21
    eqid
    #
    ip2eqi.7
    ipz
    mpan
    syl
    bitr3d
    @2
    @11
    @12
    @2
    @14
    @0
    @11
    cc
    wcel
    #
    @18
    @26
    @15
    @14
    @0
    @29
    @16
    @10
    cA
    cP
    cU
    cX
    ip2eqi.1
    ip2eqi.7
    dipcl
    mp3an1
    syl2anc
    @0
    @1
    @14
    @12
    cc
    wcel
    #
    @18
    @15
    @14
    @1
    @30
    @16
    @10
    cB
    cP
    cU
    cX
    ip2eqi.1
    ip2eqi.7
    dipcl
    mp3an1
    sylancom
    subeq0ad
    @15
    @0
    @1
    @22
    @8
    wb
    @16
    cA
    cB
    cU
    @9
    cX
    @21
    ip2eqi.1
    @17
    @28
    nvmeq0
    mp3an1
    3bitr3d
    sylibd
    @8
    @6
    vx
    cX
    cA
    cB
    @3
    cP
    oveq2
    ralrimivw
    impbid1
end
