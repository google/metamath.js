include "ccom.mm"
include "cid.mm"
include "cdif.mm"
include "cdm.mm"
include "cin.mm"
include "cun.mm"
include "inundif.mm"
include "coeq2i.mm"
include "coundi.mm"
include "eqtr3i.mm"
include "difeq1i.mm"
include "difundir.mm"
include "eqtri.mm"
include "dmeqi.mm"
include "dmun.mm"
include "wss.mm"
include "inss2.mm"
include "coss2.mm"
include "ax-mp.mm"
include "ccnv.mm"
include "cocnvcnv1.mm"
include "wrel.mm"
include "wceq.mm"
include "relcnv.mm"
include "coi1.mm"
include "cnvcnvss.mm"
include "eqsstri.mm"
include "sstri.mm"
include "ssdif.mm"
include "dmss.mm"
include "mp2b.mm"
include "difss.mm"
include "dmcoss.mm"
include "unss12.mm"
include "mp2an.mm"

theorem mvdco
  let cF: class F
  let cG: class G
  let vx: setvar x
  let vy: setvar y
  let cA: class A


  assert |- dom ( ( F o. G ) \ _I ) C_ ( dom ( F \ _I ) u. dom ( G \ _I ) )

  proof
    cF
    cG
    ccom
    #
    cid
    cdif
    #
    cdm
    #
    cF
    cG
    cid
    cin
    #
    ccom
    #
    cid
    cdif
    #
    cdm
    #
    cF
    cG
    cid
    cdif
    #
    ccom
    #
    cid
    cdif
    #
    cdm
    #
    cun
    #
    cF
    cid
    cdif
    #
    cdm
    #
    @7
    cdm
    #
    cun
    #
    @2
    @5
    @9
    cun
    #
    cdm
    @11
    @1
    @16
    @1
    @4
    @8
    cun
    #
    cid
    cdif
    @16
    @0
    @17
    cid
    cF
    @3
    @7
    cun
    #
    ccom
    @0
    @17
    @18
    cG
    cF
    cG
    cid
    inundif
    coeq2i
    cF
    @3
    @7
    coundi
    eqtr3i
    difeq1i
    @4
    @8
    cid
    difundir
    eqtri
    dmeqi
    @5
    @9
    dmun
    eqtri
    @6
    @13
    wss
    #
    @10
    @14
    wss
    @11
    @15
    wss
    @4
    cF
    wss
    @5
    @12
    wss
    @19
    @4
    cF
    cid
    ccom
    #
    cF
    @3
    cid
    wss
    @4
    @20
    wss
    cG
    cid
    inss2
    @3
    cid
    cF
    coss2
    ax-mp
    @20
    cF
    ccnv
    #
    ccnv
    #
    cF
    @22
    cid
    ccom
    #
    @20
    @22
    cF
    cid
    cocnvcnv1
    @22
    wrel
    @23
    @22
    wceq
    @21
    relcnv
    @22
    coi1
    ax-mp
    eqtr3i
    cF
    cnvcnvss
    eqsstri
    sstri
    @4
    cF
    cid
    ssdif
    @5
    @12
    dmss
    mp2b
    @10
    @8
    cdm
    #
    @14
    @9
    @8
    wss
    @10
    @24
    wss
    @8
    cid
    difss
    @9
    @8
    dmss
    ax-mp
    cF
    @7
    dmcoss
    sstri
    @6
    @13
    @10
    @14
    unss12
    mp2an
    eqsstri
end
