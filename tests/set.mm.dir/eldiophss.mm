include "cdioph.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "cc0.mm"
include "wa.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "cmzp.mm"
include "wss.mm"
include "eldioph3b.mm"
include "simpr.mm"
include "vex.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "elab.mm"
include "elfznn.mm"
include "ssriv.mm"
include "elmapssres.mm"
include "mpan2.mm"
include "ad2antlr.mm"
include "eqeltrd.mm"
include "ex.mm"
include "adantrd.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "adantr.mm"
include "eqsstrd.mm"
include "r19.29an.mm"
include "sylbi.mm"

theorem eldiophss
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d


  assert |- ( A e. ( Dioph ` B ) -> A C_ ( NN0 ^m ( 1 ... B ) ) )

  proof
    cA
    cB
    cdioph
    cfv
    wcel
    cB
    cn0
    wcel
    #
    cA
    vb
    cv
    #
    vc
    cv
    #
    c1
    cB
    cfz
    co
    #
    cres
    #
    wceq
    #
    @2
    va
    cv
    #
    cfv
    cc0
    wceq
    #
    wa
    #
    vc
    cn0
    cn
    cmap
    co
    #
    wrex
    #
    vb
    cab
    #
    wceq
    #
    va
    cn
    cmzp
    cfv
    #
    wrex
    wa
    cA
    cn0
    @3
    cmap
    co
    #
    wss
    #
    vc
    vb
    cA
    cB
    va
    eldioph3b
    @0
    @12
    @15
    va
    @13
    @0
    @6
    @13
    wcel
    wa
    #
    @12
    wa
    cA
    @11
    @14
    @16
    @12
    simpr
    @16
    @11
    @14
    wss
    @12
    @16
    vd
    @11
    @14
    vd
    cv
    #
    @11
    wcel
    @17
    @4
    wceq
    #
    @7
    wa
    #
    vc
    @9
    wrex
    #
    @16
    @17
    @14
    wcel
    #
    @10
    @20
    vb
    @17
    vd
    vex
    @1
    @17
    wceq
    #
    @8
    @19
    vc
    @9
    @22
    @5
    @18
    @7
    @1
    @17
    @4
    eqeq1
    anbi1d
    rexbidv
    elab
    @16
    @19
    @21
    vc
    @9
    @16
    @2
    @9
    wcel
    #
    wa
    #
    @18
    @21
    @7
    @24
    @18
    @21
    @24
    @18
    wa
    @17
    @4
    @14
    @24
    @18
    simpr
    @23
    @4
    @14
    wcel
    #
    @16
    @18
    @23
    @3
    cn
    wss
    @25
    va
    @3
    cn
    @6
    cB
    elfznn
    ssriv
    @2
    cn0
    cn
    @3
    elmapssres
    mpan2
    ad2antlr
    eqeltrd
    ex
    adantrd
    rexlimdva
    syl5bi
    ssrdv
    adantr
    eqsstrd
    r19.29an
    sylbi
end
