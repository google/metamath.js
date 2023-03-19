include "ccnv.mm"
include "wfun.mm"
include "cres.mm"
include "wfo.mm"
include "w3a.mm"
include "cdif.mm"
include "wf1o.mm"
include "cin.mm"
include "resdif.mm"
include "f1ofo.mm"
include "syl.mm"
include "syld3an3.mm"
include "wceq.mm"
include "wb.mm"
include "dfin4.mm"
include "f1oeq3.mm"
include "ax-mp.mm"
include "f1oeq2.mm"
include "reseq2i.mm"
include "f1oeq1.mm"
include "3bitrri.mm"
include "sylib.mm"

theorem resin
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( Fun `' F /\ ( F |` A ) : A -onto-> C /\ ( F |` B ) : B -onto-> D ) -> ( F |` ( A i^i B ) ) : ( A i^i B ) -1-1-onto-> ( C i^i D ) )

  proof
    cF
    ccnv
    wfun
    #
    cA
    cC
    cF
    cA
    cres
    wfo
    #
    cB
    cD
    cF
    cB
    cres
    wfo
    #
    w3a
    #
    cA
    cA
    cB
    cdif
    #
    cdif
    #
    cC
    cC
    cD
    cdif
    #
    cdif
    #
    cF
    @5
    cres
    #
    wf1o
    #
    cA
    cB
    cin
    #
    cC
    cD
    cin
    #
    cF
    @10
    cres
    #
    wf1o
    #
    @0
    @1
    @2
    @4
    @6
    cF
    @4
    cres
    #
    wfo
    #
    @9
    @3
    @4
    @6
    @14
    wf1o
    @15
    cA
    cB
    cC
    cD
    cF
    resdif
    @4
    @6
    @14
    f1ofo
    syl
    cA
    @4
    cC
    @6
    cF
    resdif
    syld3an3
    @13
    @10
    @7
    @12
    wf1o
    #
    @5
    @7
    @12
    wf1o
    #
    @9
    @11
    @7
    wceq
    @13
    @16
    wb
    cC
    cD
    dfin4
    @11
    @7
    @10
    @12
    f1oeq3
    ax-mp
    @10
    @5
    wceq
    @16
    @17
    wb
    cA
    cB
    dfin4
    #
    @10
    @5
    @7
    @12
    f1oeq2
    ax-mp
    @12
    @8
    wceq
    @17
    @9
    wb
    @10
    @5
    cF
    @18
    reseq2i
    @5
    @7
    @12
    @8
    f1oeq1
    ax-mp
    3bitrri
    sylib
end
