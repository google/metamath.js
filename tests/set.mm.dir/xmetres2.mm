include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cxp.mm"
include "cres.mm"
include "cdm.mm"
include "elfvdm.mm"
include "adantr.mm"
include "simpr.mm"
include "ssexd.mm"
include "cxr.mm"
include "wf.mm"
include "xmetf.mm"
include "xpss12.mm"
include "sylancom.mm"
include "fssresd.mm"
include "cv.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "ovres.mm"
include "adantl.mm"
include "eqeq1d.mm"
include "wb.mm"
include "simpll.mm"
include "simplr.mm"
include "simprl.mm"
include "sseldd.mm"
include "simprr.mm"
include "xmeteq0.mm"
include "syl3anc.mm"
include "bitrd.mm"
include "w3a.mm"
include "cxad.mm"
include "cle.mm"
include "wbr.mm"
include "simpr3.mm"
include "3adantr3.mm"
include "xmettri2.mm"
include "syl13anc.mm"
include "simpr1.mm"
include "ovresd.mm"
include "simpr2.mm"
include "oveq12d.mm"
include "3brtr4d.mm"
include "isxmetd.mm"

theorem xmetres2
  let cD: class D
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vd: setvar d
  let vw: setvar w
  let cC: class C


  assert |- ( ( D e. ( *Met ` X ) /\ R C_ X ) -> ( D |` ( R X. R ) ) e. ( *Met ` R ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cR
    cX
    wss
    #
    wa
    #
    vx
    vy
    vz
    cD
    cR
    cR
    cxp
    #
    cres
    #
    cR
    @2
    cR
    cX
    cxmt
    cdm
    #
    @0
    cX
    @5
    wcel
    @1
    cD
    cX
    cxmt
    elfvdm
    adantr
    @0
    @1
    simpr
    #
    ssexd
    @2
    cX
    cX
    cxp
    #
    cxr
    @3
    cD
    @0
    @7
    cxr
    cD
    wf
    @1
    cD
    cX
    xmetf
    adantr
    @0
    @1
    @1
    @3
    @7
    wss
    @6
    cR
    cX
    cR
    cX
    xpss12
    sylancom
    fssresd
    @2
    vx
    cv
    #
    cR
    wcel
    #
    vy
    cv
    #
    cR
    wcel
    #
    wa
    #
    wa
    #
    @8
    @10
    @4
    co
    #
    cc0
    wceq
    @8
    @10
    cD
    co
    #
    cc0
    wceq
    #
    @8
    @10
    wceq
    #
    @13
    @14
    @15
    cc0
    @12
    @14
    @15
    wceq
    #
    @2
    @8
    @10
    cR
    cR
    cD
    ovres
    adantl
    #
    eqeq1d
    @13
    @0
    @8
    cX
    wcel
    #
    @10
    cX
    wcel
    #
    @16
    @17
    wb
    @0
    @1
    @12
    simpll
    @13
    cR
    cX
    @8
    @0
    @1
    @12
    simplr
    #
    @2
    @9
    @11
    simprl
    sseldd
    #
    @13
    cR
    cX
    @10
    @22
    @2
    @9
    @11
    simprr
    sseldd
    #
    @8
    @10
    cD
    cX
    xmeteq0
    syl3anc
    bitrd
    @2
    @9
    @11
    vz
    cv
    #
    cR
    wcel
    #
    w3a
    #
    wa
    #
    @15
    @25
    @8
    cD
    co
    #
    @25
    @10
    cD
    co
    #
    cxad
    co
    #
    @14
    @25
    @8
    @4
    co
    #
    @25
    @10
    @4
    co
    #
    cxad
    co
    cle
    @28
    @0
    @25
    cX
    wcel
    @20
    @21
    @15
    @31
    cle
    wbr
    @0
    @1
    @27
    simpll
    @28
    cR
    cX
    @25
    @0
    @1
    @27
    simplr
    @2
    @9
    @11
    @26
    simpr3
    #
    sseldd
    @2
    @9
    @11
    @20
    @26
    @23
    3adantr3
    @2
    @9
    @11
    @21
    @26
    @24
    3adantr3
    @8
    @10
    @25
    cD
    cX
    xmettri2
    syl13anc
    @2
    @9
    @11
    @18
    @26
    @19
    3adantr3
    @28
    @32
    @29
    @33
    @30
    cxad
    @28
    @25
    @8
    cD
    cR
    @34
    @2
    @9
    @11
    @26
    simpr1
    ovresd
    @28
    @25
    @10
    cD
    cR
    @34
    @2
    @9
    @11
    @26
    simpr2
    ovresd
    oveq12d
    3brtr4d
    isxmetd
end
