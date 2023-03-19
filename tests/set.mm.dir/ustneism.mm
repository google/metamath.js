include "cxp.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cima.mm"
include "ccom.mm"
include "ccnv.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "snnzg.mm"
include "adantl.mm"
include "xpco.mm"
include "syl.mm"
include "cnvxp.mm"
include "cres.mm"
include "ressn.mm"
include "cnveqi.mm"
include "resss.mm"
include "cnvss.mm"
include "ax-mp.mm"
include "eqsstr3i.mm"
include "coss2.mm"
include "mp1i.mm"
include "coss1.mm"
include "sstrd.mm"
include "eqsstr3d.mm"

theorem ustneism
  let cA: class A
  let cV: class V
  let cX: class X


  assert |- ( ( V C_ ( X X. X ) /\ A e. X ) -> ( ( V " { A } ) X. ( V " { A } ) ) C_ ( V o. `' V ) )

  proof
    cV
    cX
    cX
    cxp
    wss
    #
    cA
    cX
    wcel
    #
    wa
    #
    cV
    cA
    csn
    #
    cima
    #
    @4
    cxp
    #
    @3
    @4
    cxp
    #
    @4
    @3
    cxp
    #
    ccom
    #
    cV
    cV
    ccnv
    #
    ccom
    #
    @2
    @3
    c0
    wne
    #
    @8
    @5
    wceq
    @1
    @11
    @0
    cA
    cX
    snnzg
    adantl
    @4
    @3
    @4
    xpco
    syl
    @2
    @8
    @6
    @9
    ccom
    #
    @10
    @7
    @9
    wss
    @8
    @12
    wss
    @2
    @7
    @6
    ccnv
    #
    @9
    @3
    @4
    cnvxp
    @13
    cV
    @3
    cres
    #
    ccnv
    #
    @9
    @14
    @6
    cV
    cA
    ressn
    #
    cnveqi
    @14
    cV
    wss
    @15
    @9
    wss
    cV
    @3
    resss
    #
    @14
    cV
    cnvss
    ax-mp
    eqsstr3i
    eqsstr3i
    @7
    @9
    @6
    coss2
    mp1i
    @6
    cV
    wss
    @12
    @10
    wss
    @2
    @6
    @14
    cV
    @16
    @17
    eqsstr3i
    @6
    cV
    @9
    coss1
    mp1i
    sstrd
    eqsstr3d
end
