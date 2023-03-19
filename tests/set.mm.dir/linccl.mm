include "clmod.mm"
include "wcel.mm"
include "cfn.mm"
include "wss.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "wa.mm"
include "clinc.mm"
include "cfv.mm"
include "cv.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csca.mm"
include "cbs.mm"
include "cpw.mm"
include "wceq.mm"
include "simpl.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "sseq2i.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "ssex.mm"
include "elpwg.mm"
include "syl.mm"
include "ibir.mm"
include "sylbi.mm"
include "3ad2ant2.mm"
include "lincval.mm"
include "syl3anc.mm"
include "c0g.mm"
include "eqid.mm"
include "ccmn.mm"
include "lmodcmn.mm"
include "adantr.mm"
include "simpr1.mm"
include "wi.mm"
include "wf.mm"
include "eqeltri.mm"
include "elmapg.mm"
include "mpan.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl6bi.mm"
include "imp.mm"
include "3adant2.mm"
include "ssel.mm"
include "lmodvscl.mm"
include "fmptd.mm"
include "cfsupp.mm"
include "wbr.mm"
include "anim2i.mm"
include "simpr3.mm"
include "elmapi.mm"
include "fvexd.mm"
include "fdmfifsupp.mm"
include "scmfsupp.mm"
include "gsumcl.mm"
include "eqeltrd.mm"

theorem linccl
  let cB: class B
  let cR: class R
  let cS: class S
  let cM: class M
  let cV: class V
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x
  assume linccl.b: |- B = ( Base ` M )
  assume linccl.r: |- R = ( Base ` ( Scalar ` M ) )


  assert |- ( ( M e. LMod /\ ( V e. Fin /\ V C_ B /\ S e. ( R ^m V ) ) ) -> ( S ( linC ` M ) V ) e. B )

  proof
    cM
    clmod
    wcel
    #
    cV
    cfn
    wcel
    #
    cV
    cB
    wss
    #
    cS
    cR
    cV
    cmap
    co
    #
    wcel
    #
    w3a
    #
    wa
    #
    cS
    cV
    cM
    clinc
    cfv
    co
    #
    cM
    vv
    cV
    vv
    cv
    #
    cS
    cfv
    #
    @8
    cM
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cB
    @6
    @0
    cS
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    cV
    cmap
    co
    #
    wcel
    #
    cV
    cM
    cbs
    cfv
    #
    cpw
    wcel
    #
    @7
    @13
    wceq
    @0
    @5
    simpl
    #
    @5
    @17
    @0
    @4
    @1
    @17
    @2
    @4
    @17
    @3
    @16
    cS
    cR
    @15
    cV
    cmap
    linccl.r
    oveq1i
    eleq2i
    biimpi
    3ad2ant3
    adantl
    @5
    @19
    @0
    @2
    @1
    @19
    @4
    @2
    cV
    @18
    wss
    #
    @19
    cB
    @18
    cV
    linccl.b
    sseq2i
    @21
    @19
    @21
    cV
    cvv
    wcel
    @19
    @21
    wb
    cV
    @18
    cM
    cbs
    fvex
    ssex
    cV
    @18
    cvv
    elpwg
    syl
    ibir
    sylbi
    3ad2ant2
    #
    adantl
    vv
    cS
    cM
    cV
    clmod
    lincval
    syl3anc
    @6
    cV
    cB
    @12
    cM
    cfn
    cM
    c0g
    cfv
    #
    linccl.b
    @23
    eqid
    @0
    cM
    ccmn
    wcel
    @5
    cM
    lmodcmn
    adantr
    @0
    @1
    @2
    @4
    simpr1
    #
    @6
    vv
    cV
    @11
    cB
    @12
    @6
    @8
    cV
    wcel
    #
    wa
    @0
    @9
    cR
    wcel
    #
    @8
    cB
    wcel
    #
    @11
    cB
    wcel
    @6
    @0
    @25
    @20
    adantr
    @6
    @25
    @26
    @5
    @25
    @26
    wi
    #
    @0
    @1
    @4
    @28
    @2
    @1
    @4
    @28
    @1
    @4
    cV
    cR
    cS
    wf
    #
    @28
    cR
    cvv
    wcel
    @1
    @4
    @29
    wb
    cR
    @15
    cvv
    linccl.r
    @14
    cbs
    fvex
    eqeltri
    cR
    cV
    cS
    cvv
    cfn
    elmapg
    mpan
    @29
    @25
    @26
    cV
    cR
    @8
    cS
    ffvelrn
    ex
    syl6bi
    imp
    3adant2
    adantl
    imp
    @6
    @25
    @27
    @5
    @25
    @27
    wi
    #
    @0
    @2
    @1
    @30
    @4
    cV
    cB
    @8
    ssel
    3ad2ant2
    adantl
    imp
    @9
    @10
    @14
    cR
    cB
    cM
    @8
    linccl.b
    @14
    eqid
    #
    @10
    eqid
    linccl.r
    lmodvscl
    syl3anc
    @12
    eqid
    fmptd
    @6
    @0
    @19
    wa
    @4
    cS
    @14
    c0g
    cfv
    #
    cfsupp
    wbr
    @12
    @23
    cfsupp
    wbr
    @5
    @19
    @0
    @22
    anim2i
    @0
    @1
    @2
    @4
    simpr3
    @6
    cV
    cR
    cS
    cvv
    @32
    @5
    @29
    @0
    @4
    @1
    @29
    @2
    cS
    cR
    cV
    elmapi
    3ad2ant3
    adantl
    @24
    @6
    @14
    c0g
    fvexd
    fdmfifsupp
    vv
    cS
    cR
    @14
    cM
    cV
    @31
    linccl.r
    scmfsupp
    syl3anc
    gsumcl
    eqeltrd
end
