include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "cvtx.mm"
include "cfv.mm"
include "cedg.mm"
include "wa.mm"
include "cuspgr.mm"
include "wrex.mm"
include "copab.mm"
include "cxp.mm"
include "wb.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "adantr.mm"
include "biimpac.mm"
include "wi.mm"
include "w3a.mm"
include "cspr.mm"
include "cpw.mm"
include "wss.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "upgredgssspr.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "simp2l.mm"
include "simp3.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "sseqtrd.mm"
include "fvex.mm"
include "elpw.mm"
include "sylibr.mm"
include "simpr.mm"
include "eqcomd.mm"
include "3ad2ant2.mm"
include "a1i.mm"
include "3eltr4d.mm"
include "3exp.mm"
include "rexlimiv.mm"
include "impcom.mm"
include "adantl.mm"
include "opabssxpd.mm"
include "syl5eqss.mm"

theorem uspgropssxp
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let cG: class G
  let cV: class V
  let cW: class W
  let vq: setvar q
  let vk: setvar k
  let vx: setvar x
  assume uspgrsprf.p: |- P = ~P ( Pairs ` V )
  assume uspgrsprf.g: |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) }

  disjoint P e
  disjoint P q
  disjoint P v
  disjoint e q
  disjoint e v
  disjoint q v
  disjoint V e
  disjoint V q
  disjoint V v
  disjoint W e
  disjoint W v
  disjoint k x
  assert |- ( V e. W -> G C_ ( W X. P ) )

  proof
    cV
    cW
    wcel
    #
    cG
    vv
    cv
    #
    cV
    wceq
    #
    vq
    cv
    #
    cvtx
    cfv
    #
    @1
    wceq
    #
    @3
    cedg
    cfv
    #
    ve
    cv
    #
    wceq
    #
    wa
    #
    vq
    cuspgr
    wrex
    #
    wa
    #
    vv
    ve
    copab
    cW
    cP
    cxp
    uspgrsprf.g
    @0
    @11
    vv
    ve
    cW
    cP
    @11
    @0
    @1
    cW
    wcel
    #
    @2
    @0
    @12
    wb
    #
    @10
    @13
    cV
    @1
    cV
    @1
    cW
    eleq1
    eqcoms
    adantr
    biimpac
    @11
    @7
    cP
    wcel
    #
    @0
    @10
    @2
    @14
    @9
    @2
    @14
    wi
    vq
    cuspgr
    @3
    cuspgr
    wcel
    #
    @9
    @2
    @14
    @15
    @9
    @2
    w3a
    #
    @6
    cV
    cspr
    cfv
    #
    cpw
    #
    @7
    cP
    @16
    @6
    @17
    wss
    @6
    @18
    wcel
    @16
    @6
    @4
    cspr
    cfv
    #
    @17
    @15
    @9
    @6
    @19
    wss
    #
    @2
    @15
    @3
    cupgr
    wcel
    @20
    @3
    uspgrupgr
    @3
    upgredgssspr
    syl
    3ad2ant1
    @16
    @4
    cV
    cspr
    @16
    @4
    @1
    cV
    @15
    @5
    @8
    @2
    simp2l
    @15
    @9
    @2
    simp3
    eqtrd
    fveq2d
    sseqtrd
    @6
    @17
    @3
    cedg
    fvex
    elpw
    sylibr
    @9
    @15
    @7
    @6
    wceq
    @2
    @9
    @6
    @7
    @5
    @8
    simpr
    eqcomd
    3ad2ant2
    cP
    @18
    wceq
    @16
    uspgrsprf.p
    a1i
    3eltr4d
    3exp
    rexlimiv
    impcom
    adantl
    opabssxpd
    syl5eqss
end
