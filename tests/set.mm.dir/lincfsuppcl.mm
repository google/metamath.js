include "clmod.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cfsupp.mm"
include "wbr.mm"
include "w3a.mm"
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
include "simp1.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "adantr.mm"
include "3ad2ant3.mm"
include "elpwg.mm"
include "a1i.mm"
include "eqcomd.mm"
include "sseq2d.mm"
include "bitr2d.mm"
include "biimpa.mm"
include "3ad2ant2.mm"
include "lincval.mm"
include "syl3anc.mm"
include "c0g.mm"
include "eqid.mm"
include "ccmn.mm"
include "lmodcmn.mm"
include "3ad2ant1.mm"
include "simpl.mm"
include "wi.mm"
include "wf.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "ex.mm"
include "syl.mm"
include "imp.mm"
include "ssel.mm"
include "adantl.mm"
include "lmodvscl.mm"
include "fmptd.mm"
include "simp3r.mm"
include "syl6breq.mm"
include "scmfsupp.mm"
include "syl211anc.mm"
include "gsumcl.mm"
include "eqeltrd.mm"

theorem lincfsuppcl
  let cB: class B
  let cR: class R
  let cS: class S
  let cF: class F
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vv: setvar v
  let vk: setvar k
  let vx: setvar x
  assume lincfsuppcl.b: |- B = ( Base ` M )
  assume lincfsuppcl.r: |- R = ( Scalar ` M )
  assume lincfsuppcl.s: |- S = ( Base ` R )
  assume lincfsuppcl.0: |- .0. = ( 0g ` R )


  assert |- ( ( M e. LMod /\ ( V e. W /\ V C_ B ) /\ ( F e. ( S ^m V ) /\ F finSupp .0. ) ) -> ( F ( linC ` M ) V ) e. B )

  proof
    cM
    clmod
    wcel
    #
    cV
    cW
    wcel
    #
    cV
    cB
    wss
    #
    wa
    #
    cF
    cS
    cV
    cmap
    co
    #
    wcel
    #
    cF
    c.0
    cfsupp
    wbr
    #
    wa
    #
    w3a
    #
    cF
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
    cF
    cfv
    #
    @10
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
    @8
    @0
    cF
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
    @9
    @15
    wceq
    @0
    @3
    @7
    simp1
    #
    @7
    @0
    @19
    @3
    @5
    @19
    @6
    @5
    @19
    @4
    @18
    cF
    cS
    @17
    cV
    cmap
    cS
    cR
    cbs
    cfv
    @17
    lincfsuppcl.s
    cR
    @16
    cbs
    lincfsuppcl.r
    fveq2i
    eqtri
    oveq1i
    eleq2i
    biimpi
    adantr
    3ad2ant3
    @3
    @0
    @21
    @7
    @1
    @2
    @21
    @1
    @21
    cV
    @20
    wss
    @2
    cV
    @20
    cW
    elpwg
    @1
    @20
    cB
    cV
    @1
    cB
    @20
    cB
    @20
    wceq
    @1
    lincfsuppcl.b
    a1i
    eqcomd
    sseq2d
    bitr2d
    biimpa
    3ad2ant2
    #
    vv
    cF
    cM
    cV
    clmod
    lincval
    syl3anc
    @8
    cV
    cB
    @14
    cM
    cW
    cM
    c0g
    cfv
    #
    lincfsuppcl.b
    @24
    eqid
    @0
    @3
    cM
    ccmn
    wcel
    @7
    cM
    lmodcmn
    3ad2ant1
    @3
    @0
    @1
    @7
    @1
    @2
    simpl
    3ad2ant2
    @8
    vv
    cV
    @13
    cB
    @14
    @8
    @10
    cV
    wcel
    #
    wa
    @0
    @11
    cS
    wcel
    #
    @10
    cB
    wcel
    #
    @13
    cB
    wcel
    @8
    @0
    @25
    @22
    adantr
    @8
    @25
    @26
    @7
    @0
    @25
    @26
    wi
    #
    @3
    @5
    @28
    @6
    @5
    cV
    cS
    cF
    wf
    #
    @28
    cF
    cS
    cV
    elmapi
    @29
    @25
    @26
    cV
    cS
    @10
    cF
    ffvelrn
    ex
    syl
    adantr
    3ad2ant3
    imp
    @8
    @25
    @27
    @3
    @0
    @25
    @27
    wi
    #
    @7
    @2
    @30
    @1
    cV
    cB
    @10
    ssel
    adantl
    3ad2ant2
    imp
    @11
    @12
    cR
    cS
    cB
    cM
    @10
    lincfsuppcl.b
    lincfsuppcl.r
    @12
    eqid
    lincfsuppcl.s
    lmodvscl
    syl3anc
    @14
    eqid
    fmptd
    @8
    @0
    @21
    @5
    cF
    cR
    c0g
    cfv
    #
    cfsupp
    wbr
    @14
    @24
    cfsupp
    wbr
    @22
    @23
    @7
    @0
    @5
    @3
    @5
    @6
    simpl
    3ad2ant3
    @8
    cF
    c.0
    @31
    cfsupp
    @0
    @3
    @5
    @6
    simp3r
    lincfsuppcl.0
    syl6breq
    vv
    cF
    cS
    cR
    cM
    cV
    lincfsuppcl.r
    lincfsuppcl.s
    scmfsupp
    syl211anc
    gsumcl
    eqeltrd
end
