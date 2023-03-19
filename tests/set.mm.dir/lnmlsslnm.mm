include "clnm.mm"
include "wcel.mm"
include "wa.mm"
include "clmod.mm"
include "cv.mm"
include "cress.mm"
include "co.mm"
include "clfig.mm"
include "clss.mm"
include "cfv.mm"
include "wral.mm"
include "lnmlmod.mm"
include "lsslmod.mm"
include "sylan.mm"
include "oveq1i.mm"
include "wss.mm"
include "wceq.mm"
include "simplr.mm"
include "cbs.mm"
include "eqid.mm"
include "lssss.mm"
include "adantl.mm"
include "ressbas2.mm"
include "syl.mm"
include "ad2antlr.mm"
include "sseqtr4d.mm"
include "ressabs.mm"
include "syl2anc.mm"
include "syl5eq.mm"
include "simpll.mm"
include "wb.mm"
include "lsslss.mm"
include "simprbda.mm"
include "lnmlssfg.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "islnm.mm"
include "sylanbrc.mm"

theorem lnmlsslnm
  let cR: class R
  let cS: class S
  let cU: class U
  let cM: class M
  let va: setvar a
  assume lnmlssfg.s: |- S = ( LSubSp ` M )
  assume lnmlssfg.r: |- R = ( M |`s U )


  assert |- ( ( M e. LNoeM /\ U e. S ) -> R e. LNoeM )

  proof
    cM
    clnm
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cR
    clmod
    wcel
    #
    cR
    va
    cv
    #
    cress
    co
    #
    clfig
    wcel
    #
    va
    cR
    clss
    cfv
    #
    wral
    cR
    clnm
    wcel
    @0
    cM
    clmod
    wcel
    #
    @1
    @3
    cM
    lnmlmod
    #
    cS
    cU
    cM
    cR
    lnmlssfg.r
    lnmlssfg.s
    lsslmod
    sylan
    @2
    @6
    va
    @7
    @2
    @4
    @7
    wcel
    #
    wa
    #
    @5
    cM
    @4
    cress
    co
    #
    clfig
    @11
    @5
    cM
    cU
    cress
    co
    #
    @4
    cress
    co
    #
    @12
    cR
    @13
    @4
    cress
    lnmlssfg.r
    oveq1i
    @11
    @1
    @4
    cU
    wss
    #
    @14
    @12
    wceq
    @0
    @1
    @10
    simplr
    @11
    @4
    cR
    cbs
    cfv
    #
    cU
    @10
    @4
    @16
    wss
    @2
    @7
    @4
    @16
    cR
    @16
    eqid
    @7
    eqid
    #
    lssss
    adantl
    @1
    cU
    @16
    wceq
    #
    @0
    @10
    @1
    cU
    cM
    cbs
    cfv
    #
    wss
    @18
    cS
    cU
    @19
    cM
    @19
    eqid
    #
    lnmlssfg.s
    lssss
    cU
    @19
    cR
    cM
    lnmlssfg.r
    @20
    ressbas2
    syl
    ad2antlr
    sseqtr4d
    cU
    @4
    cM
    cS
    ressabs
    syl2anc
    syl5eq
    @11
    @0
    @4
    cS
    wcel
    #
    @12
    clfig
    wcel
    @0
    @1
    @10
    simpll
    @2
    @10
    @21
    @15
    @0
    @8
    @1
    @10
    @21
    @15
    wa
    wb
    @9
    cS
    @7
    cU
    @4
    cM
    cR
    lnmlssfg.r
    lnmlssfg.s
    @17
    lsslss
    sylan
    simprbda
    @12
    cS
    @4
    cM
    lnmlssfg.s
    @12
    eqid
    lnmlssfg
    syl2anc
    eqeltrd
    ralrimiva
    @7
    va
    cR
    @17
    islnm
    sylanbrc
end
