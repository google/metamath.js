include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "crp.mm"
include "wa.mm"
include "cv.mm"
include "cxdiv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cdm.mm"
include "c1.mm"
include "wceq.mm"
include "cprb.mm"
include "measdivcstOLD.mm"
include "cvv.mm"
include "wral.mm"
include "ovex.mm"
include "rgenw.mm"
include "dmmptg.mm"
include "ax-mp.mm"
include "fveq2i.mm"
include "syl6eleqr.mm"
include "measbasedom.mm"
include "sylibr.mm"
include "unieqi.mm"
include "csiga.mm"
include "measbase.mm"
include "cdif.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "cpw.mm"
include "wss.mm"
include "w3a.mm"
include "isrnsigau.mm"
include "simprd.mm"
include "simp1d.mm"
include "syl.mm"
include "id.mm"
include "rpxdivcld.mm"
include "anim12i.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "eqid.mm"
include "fvmptg.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "rpre.mm"
include "rpne0.mm"
include "xdivid.mm"
include "syl2anc.mm"
include "adantl.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "elprob.mm"
include "sylanbrc.mm"

theorem probfinmeasbOLD
  let vx: setvar x
  let cS: class S
  let cM: class M
  let vy: setvar y

  disjoint M x
  disjoint S x
  disjoint x y
  disjoint S y
  assert |- ( ( M e. ( measures ` S ) /\ ( M ` U. S ) e. RR+ ) -> ( x e. S |-> ( ( M ` x ) /e ( M ` U. S ) ) ) e. Prob )

  proof
    cM
    cS
    cmeas
    cfv
    #
    wcel
    #
    cS
    cuni
    #
    cM
    cfv
    #
    crp
    wcel
    #
    wa
    #
    vx
    cS
    vx
    cv
    #
    cM
    cfv
    #
    @3
    cxdiv
    co
    #
    cmpt
    #
    cmeas
    crn
    cuni
    wcel
    #
    @9
    cdm
    #
    cuni
    #
    @9
    cfv
    #
    c1
    wceq
    @9
    cprb
    wcel
    @5
    @9
    @11
    cmeas
    cfv
    #
    wcel
    @10
    @5
    @9
    @0
    @14
    vx
    @3
    cS
    cM
    measdivcstOLD
    @11
    cS
    cmeas
    @8
    cvv
    wcel
    #
    vx
    cS
    wral
    @11
    cS
    wceq
    @15
    vx
    cS
    @7
    @3
    cxdiv
    ovex
    rgenw
    vx
    cS
    @8
    cvv
    dmmptg
    ax-mp
    #
    fveq2i
    syl6eleqr
    @9
    measbasedom
    sylibr
    @5
    @13
    @2
    @9
    cfv
    #
    c1
    @12
    @2
    @9
    @11
    cS
    @16
    unieqi
    fveq2i
    @5
    @17
    @3
    @3
    cxdiv
    co
    #
    c1
    @5
    @2
    cS
    wcel
    #
    @18
    crp
    wcel
    #
    wa
    @17
    @18
    wceq
    @1
    @19
    @4
    @20
    @1
    cS
    csiga
    crn
    cuni
    wcel
    #
    @19
    cS
    cM
    measbase
    @21
    @19
    @2
    vy
    cv
    #
    cdif
    cS
    wcel
    vy
    cS
    wral
    #
    @22
    com
    cdom
    wbr
    @22
    cuni
    cS
    wcel
    wi
    vy
    cS
    cpw
    wral
    #
    @21
    cS
    @2
    cpw
    wss
    @19
    @23
    @24
    w3a
    vy
    cS
    isrnsigau
    simprd
    simp1d
    syl
    @4
    @3
    @3
    @4
    id
    #
    @25
    rpxdivcld
    anim12i
    vx
    @2
    @8
    @18
    cS
    crp
    @9
    @6
    @2
    wceq
    @7
    @3
    @3
    cxdiv
    @6
    @2
    cM
    fveq2
    oveq1d
    @9
    eqid
    fvmptg
    syl
    @4
    @18
    c1
    wceq
    #
    @1
    @4
    @3
    cr
    wcel
    @3
    cc0
    wne
    @26
    @3
    rpre
    @3
    rpne0
    @3
    xdivid
    syl2anc
    adantl
    eqtrd
    syl5eq
    @9
    elprob
    sylanbrc
end
