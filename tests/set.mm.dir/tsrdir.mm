include "ctsr.mm"
include "wcel.mm"
include "cdir.mm"
include "wrel.mm"
include "cid.mm"
include "cuni.mm"
include "cres.mm"
include "wss.mm"
include "wa.mm"
include "ccom.mm"
include "cxp.mm"
include "ccnv.mm"
include "cps.mm"
include "tsrps.mm"
include "psrel.mm"
include "syl.mm"
include "cin.mm"
include "psref2.mm"
include "inss1.mm"
include "syl6eqssr.mm"
include "jca.mm"
include "pstr2.mm"
include "cdm.mm"
include "wceq.mm"
include "crn.mm"
include "psdmrn.mm"
include "simpld.mm"
include "sqxpeqd.mm"
include "cun.mm"
include "eqid.mm"
include "istsr.mm"
include "simprbi.mm"
include "relcoi2.mm"
include "cnvresid.mm"
include "cnvss.mm"
include "syl5eqssr.mm"
include "coss1.mm"
include "eqsstr3d.mm"
include "relcnv.mm"
include "relcoi1.mm"
include "ax-mp.mm"
include "relcnvfld.mm"
include "reseq2d.mm"
include "coss2.mm"
include "unssd.mm"
include "sstrd.mm"
include "isdir.mm"
include "mpbir2and.mm"

theorem tsrdir
  let cA: class A


  assert |- ( A e. TosetRel -> A e. DirRel )

  proof
    cA
    ctsr
    wcel
    #
    cA
    cdir
    wcel
    cA
    wrel
    #
    cid
    cA
    cuni
    cuni
    #
    cres
    #
    cA
    wss
    #
    wa
    cA
    cA
    ccom
    cA
    wss
    #
    @2
    @2
    cxp
    #
    cA
    ccnv
    #
    cA
    ccom
    #
    wss
    #
    wa
    @0
    @1
    @4
    @0
    cA
    cps
    wcel
    #
    @1
    cA
    tsrps
    #
    cA
    psrel
    syl
    #
    @0
    @10
    @4
    @11
    @10
    @3
    cA
    @7
    cin
    cA
    cA
    psref2
    cA
    @7
    inss1
    syl6eqssr
    syl
    #
    jca
    @0
    @5
    @9
    @0
    @10
    @5
    @11
    cA
    pstr2
    syl
    @0
    @6
    cA
    cdm
    #
    @14
    cxp
    #
    @8
    @0
    @14
    @2
    @0
    @14
    @2
    wceq
    #
    cA
    crn
    @2
    wceq
    #
    @0
    @10
    @16
    @17
    wa
    @11
    cA
    psdmrn
    syl
    simpld
    sqxpeqd
    @0
    @15
    cA
    @7
    cun
    #
    @8
    @0
    @10
    @15
    @18
    wss
    cA
    @14
    @14
    eqid
    istsr
    simprbi
    @0
    cA
    @7
    @8
    @0
    cA
    @3
    cA
    ccom
    #
    @8
    @0
    @1
    @19
    cA
    wceq
    @12
    cA
    relcoi2
    syl
    @0
    @3
    @7
    wss
    @19
    @8
    wss
    @0
    @3
    @3
    ccnv
    #
    @7
    @2
    cnvresid
    @0
    @4
    @20
    @7
    wss
    @13
    @3
    cA
    cnvss
    syl
    syl5eqssr
    @3
    @7
    cA
    coss1
    syl
    eqsstr3d
    @0
    @7
    @7
    cid
    @7
    cuni
    cuni
    #
    cres
    #
    ccom
    #
    @8
    @7
    wrel
    @23
    @7
    wceq
    cA
    relcnv
    @7
    relcoi1
    ax-mp
    @0
    @22
    cA
    wss
    @23
    @8
    wss
    @0
    @22
    @3
    cA
    @0
    @2
    @21
    cid
    @0
    @1
    @2
    @21
    wceq
    @12
    cA
    relcnvfld
    syl
    reseq2d
    @13
    eqsstr3d
    @22
    cA
    @7
    coss2
    syl
    syl5eqssr
    unssd
    sstrd
    eqsstr3d
    jca
    @2
    cA
    ctsr
    @2
    eqid
    isdir
    mpbir2and
end
