include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "wcel.mm"
include "cop.mm"
include "wceq.mm"
include "cvtx.mm"
include "cedg.mm"
include "wa.mm"
include "cuspgr.mm"
include "wrex.mm"
include "wex.mm"
include "copab.mm"
include "eleq2i.mm"
include "elopab.mm"
include "bitri.mm"
include "cspr.mm"
include "wss.mm"
include "cupgr.mm"
include "uspgrupgr.mm"
include "upgredgssspr.mm"
include "syl.mm"
include "adantr.mm"
include "wb.mm"
include "simpr.mm"
include "fveq2.mm"
include "sseq12d.mm"
include "adantl.mm"
include "mpbid.mm"
include "rexlimiva.mm"
include "sseq2d.mm"
include "vex.mm"
include "op2ndd.mm"
include "sseq1d.mm"
include "mpbird.mm"
include "cpw.mm"
include "fvex.mm"
include "elpw.mm"
include "sylibr.mm"
include "exlimivv.mm"
include "sylbi.mm"
include "fmpti.mm"

theorem uspgrsprf
  let vv: setvar v
  let cP: class P
  let ve: setvar e
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cV: class V
  let vq: setvar q
  let cX: class X
  let cW: class W
  let vk: setvar k
  let vx: setvar x
  assume uspgrsprf.p: |- P = ~P ( Pairs ` V )
  assume uspgrsprf.g: |- G = { <. v , e >. | ( v = V /\ E. q e. USPGraph ( ( Vtx ` q ) = v /\ ( Edg ` q ) = e ) ) }
  assume uspgrsprf.f: |- F = ( g e. G |-> ( 2nd ` g ) )

  disjoint P e
  disjoint P g
  disjoint P v
  disjoint e g
  disjoint e v
  disjoint g v
  disjoint P e
  disjoint P q
  disjoint P v
  disjoint e q
  disjoint e v
  disjoint q v
  disjoint V e
  disjoint V q
  disjoint V v
  disjoint G g
  disjoint X g
  disjoint W e
  disjoint W v
  disjoint k x
  assert |- F : G --> P

  proof
    vg
    cG
    cP
    vg
    cv
    #
    c2nd
    cfv
    #
    cF
    uspgrsprf.f
    @0
    cG
    wcel
    #
    @0
    vv
    cv
    #
    ve
    cv
    #
    cop
    wceq
    #
    @3
    cV
    wceq
    #
    vq
    cv
    #
    cvtx
    cfv
    #
    @3
    wceq
    #
    @7
    cedg
    cfv
    #
    @4
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
    wa
    #
    ve
    wex
    vv
    wex
    #
    @1
    cP
    wcel
    #
    @2
    @0
    @14
    vv
    ve
    copab
    #
    wcel
    @16
    cG
    @18
    @0
    uspgrsprf.g
    eleq2i
    @14
    vv
    ve
    @0
    elopab
    bitri
    @15
    @17
    vv
    ve
    @15
    @1
    cV
    cspr
    cfv
    #
    wss
    #
    @17
    @15
    @20
    @4
    @19
    wss
    #
    @14
    @21
    @5
    @14
    @4
    @3
    cspr
    cfv
    #
    wss
    #
    @21
    @13
    @23
    @6
    @12
    @23
    vq
    cuspgr
    @7
    cuspgr
    wcel
    #
    @12
    wa
    @10
    @8
    cspr
    cfv
    #
    wss
    #
    @23
    @24
    @26
    @12
    @24
    @7
    cupgr
    wcel
    @26
    @7
    uspgrupgr
    @7
    upgredgssspr
    syl
    adantr
    @12
    @26
    @23
    wb
    @24
    @12
    @10
    @4
    @25
    @22
    @9
    @11
    simpr
    @9
    @25
    @22
    wceq
    @11
    @8
    @3
    cspr
    fveq2
    adantr
    sseq12d
    adantl
    mpbid
    rexlimiva
    adantl
    @6
    @23
    @21
    wb
    @13
    @6
    @22
    @19
    @4
    @3
    cV
    cspr
    fveq2
    sseq2d
    adantr
    mpbid
    adantl
    @5
    @20
    @21
    wb
    @14
    @5
    @1
    @4
    @19
    @3
    @4
    @0
    vv
    vex
    ve
    vex
    op2ndd
    sseq1d
    adantr
    mpbird
    @17
    @1
    @19
    cpw
    #
    wcel
    @20
    cP
    @27
    @1
    uspgrsprf.p
    eleq2i
    @1
    @19
    @0
    c2nd
    fvex
    elpw
    bitri
    sylibr
    exlimivv
    sylbi
    fmpti
end
