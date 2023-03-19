include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "ctop.mm"
include "cuni.mm"
include "ccom.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "wral.mm"
include "cntop1.mm"
include "cntop2.mm"
include "anim12i.mm"
include "eqid.mm"
include "cnf.mm"
include "fco.mm"
include "syl2anr.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "eqtri.mm"
include "simpll.mm"
include "cnima.mm"
include "adantll.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "ralrimiva.mm"
include "jca.mm"
include "iscn2.mm"
include "sylanbrc.mm"

theorem cnco
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let vx: setvar x


  assert |- ( ( F e. ( J Cn K ) /\ G e. ( K Cn L ) ) -> ( G o. F ) e. ( J Cn L ) )

  proof
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cG
    cK
    cL
    ccn
    co
    wcel
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    cL
    ctop
    wcel
    #
    wa
    cJ
    cuni
    #
    cL
    cuni
    #
    cG
    cF
    ccom
    #
    wf
    #
    @7
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cJ
    wcel
    #
    vx
    cL
    wral
    #
    wa
    @7
    cJ
    cL
    ccn
    co
    wcel
    @0
    @3
    @1
    @4
    cF
    cJ
    cK
    cntop1
    cG
    cK
    cL
    cntop2
    anim12i
    @2
    @8
    @13
    @1
    cK
    cuni
    #
    @6
    cG
    wf
    @5
    @14
    cF
    wf
    @8
    @0
    cG
    cK
    cL
    @14
    @6
    @14
    eqid
    #
    @6
    eqid
    #
    cnf
    cF
    cJ
    cK
    @5
    @14
    @5
    eqid
    #
    @15
    cnf
    @5
    @14
    @6
    cG
    cF
    fco
    syl2anr
    @2
    @12
    vx
    cL
    @2
    @10
    cL
    wcel
    #
    wa
    #
    @11
    cF
    ccnv
    #
    cG
    ccnv
    #
    @10
    cima
    #
    cima
    #
    cJ
    @11
    @20
    @21
    ccom
    #
    @10
    cima
    @23
    @9
    @24
    @10
    cG
    cF
    cnvco
    imaeq1i
    @20
    @21
    @10
    imaco
    eqtri
    @19
    @0
    @22
    cK
    wcel
    #
    @23
    cJ
    wcel
    @0
    @1
    @18
    simpll
    @1
    @18
    @25
    @0
    @10
    cG
    cK
    cL
    cnima
    adantll
    @22
    cF
    cJ
    cK
    cnima
    syl2anc
    syl5eqel
    ralrimiva
    jca
    vx
    @7
    cJ
    cL
    @5
    @6
    @17
    @16
    iscn2
    sylanbrc
end
