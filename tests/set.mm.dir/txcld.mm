include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "ctx.mm"
include "co.mm"
include "cuni.mm"
include "wss.mm"
include "cdif.mm"
include "eqid.mm"
include "cldss.mm"
include "xpss12.mm"
include "syl2an.mm"
include "ctop.mm"
include "wceq.mm"
include "cldrcl.mm"
include "txuni.mm"
include "sseqtrd.mm"
include "cun.mm"
include "difxp.mm"
include "difeq1d.mm"
include "syl5eqr.mm"
include "txtop.mm"
include "adantr.mm"
include "adantl.mm"
include "cldopn.mm"
include "topopn.mm"
include "syl.mm"
include "txopn.mm"
include "syl22anc.mm"
include "unopn.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "iscld.mm"
include "mpbir2and.mm"

theorem txcld
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S


  assert |- ( ( A e. ( Clsd ` R ) /\ B e. ( Clsd ` S ) ) -> ( A X. B ) e. ( Clsd ` ( R tX S ) ) )

  proof
    cA
    cR
    ccld
    cfv
    wcel
    #
    cB
    cS
    ccld
    cfv
    wcel
    #
    wa
    #
    cA
    cB
    cxp
    #
    cR
    cS
    ctx
    co
    #
    ccld
    cfv
    wcel
    #
    @3
    @4
    cuni
    #
    wss
    #
    @6
    @3
    cdif
    #
    @4
    wcel
    #
    @2
    @3
    cR
    cuni
    #
    cS
    cuni
    #
    cxp
    #
    @6
    @0
    cA
    @10
    wss
    cB
    @11
    wss
    @3
    @12
    wss
    @1
    cA
    cR
    @10
    @10
    eqid
    #
    cldss
    cB
    cS
    @11
    @11
    eqid
    #
    cldss
    cA
    @10
    cB
    @11
    xpss12
    syl2an
    @0
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    @12
    @6
    wceq
    @1
    cA
    cR
    cldrcl
    #
    cB
    cS
    cldrcl
    #
    cR
    cS
    @10
    @11
    @13
    @14
    txuni
    syl2an
    #
    sseqtrd
    @2
    @10
    cA
    cdif
    #
    @11
    cxp
    #
    @10
    @11
    cB
    cdif
    #
    cxp
    #
    cun
    #
    @8
    @4
    @2
    @24
    @12
    @3
    cdif
    @8
    cA
    cB
    @10
    @11
    difxp
    @2
    @12
    @6
    @3
    @19
    difeq1d
    syl5eqr
    @2
    @4
    ctop
    wcel
    #
    @21
    @4
    wcel
    #
    @23
    @4
    wcel
    #
    @24
    @4
    wcel
    @0
    @15
    @16
    @25
    @1
    @17
    @18
    cR
    cS
    txtop
    syl2an
    #
    @2
    @15
    @16
    @20
    cR
    wcel
    #
    @11
    cS
    wcel
    #
    @26
    @0
    @15
    @1
    @17
    adantr
    #
    @1
    @16
    @0
    @18
    adantl
    #
    @0
    @29
    @1
    cA
    cR
    @10
    @13
    cldopn
    adantr
    @2
    @16
    @30
    @32
    cS
    @11
    @14
    topopn
    syl
    @20
    @11
    cR
    cS
    ctop
    ctop
    txopn
    syl22anc
    @2
    @15
    @16
    @10
    cR
    wcel
    #
    @22
    cS
    wcel
    #
    @27
    @31
    @32
    @2
    @15
    @33
    @31
    cR
    @10
    @13
    topopn
    syl
    @1
    @34
    @0
    cB
    cS
    @11
    @14
    cldopn
    adantl
    @10
    @22
    cR
    cS
    ctop
    ctop
    txopn
    syl22anc
    @21
    @23
    @4
    unopn
    syl3anc
    eqeltrrd
    @2
    @25
    @5
    @7
    @9
    wa
    wb
    @28
    @3
    @4
    @6
    @6
    eqid
    iscld
    syl
    mpbir2and
end
