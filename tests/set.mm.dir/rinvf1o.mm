include "cima.mm"
include "cres.mm"
include "wf1o.mm"
include "cdm.mm"
include "crn.mm"
include "wf1.mm"
include "wss.mm"
include "wf.mm"
include "ccnv.mm"
include "wfun.mm"
include "fdmrn.mm"
include "mpbi.mm"
include "funeqi.mm"
include "mpbir.mm"
include "df-f1.mm"
include "mpbir2an.mm"
include "f1ores.mm"
include "mp2an.mm"
include "wceq.mm"
include "wb.mm"
include "funimass3.mm"
include "imaeq1i.mm"
include "sseqtri.mm"
include "eqssi.mm"
include "f1oeq3.mm"
include "ax-mp.mm"

theorem rinvf1o
  let cA: class A
  let cB: class B
  let cF: class F
  assume rinvbij.1: |- Fun F
  assume rinvbij.2: |- `' F = F
  assume rinvbij.3a: |- ( F " A ) C_ B
  assume rinvbij.3b: |- ( F " B ) C_ A
  assume rinvbij.4a: |- A C_ dom F
  assume rinvbij.4b: |- B C_ dom F


  assert |- ( F |` A ) : A -1-1-onto-> B

  proof
    cA
    cF
    cA
    cima
    #
    cF
    cA
    cres
    #
    wf1o
    #
    cA
    cB
    @1
    wf1o
    #
    cF
    cdm
    #
    cF
    crn
    #
    cF
    wf1
    #
    cA
    @4
    wss
    @2
    @6
    @4
    @5
    cF
    wf
    #
    cF
    ccnv
    #
    wfun
    #
    cF
    wfun
    #
    @7
    rinvbij.1
    cF
    fdmrn
    mpbi
    @9
    @10
    rinvbij.1
    @8
    cF
    rinvbij.2
    funeqi
    mpbir
    @4
    @5
    cF
    df-f1
    mpbir2an
    rinvbij.4a
    @4
    @5
    cA
    cF
    f1ores
    mp2an
    @0
    cB
    wceq
    @2
    @3
    wb
    @0
    cB
    rinvbij.3a
    cB
    @8
    cA
    cima
    #
    @0
    cF
    cB
    cima
    cA
    wss
    #
    cB
    @11
    wss
    #
    rinvbij.3b
    @10
    cB
    @4
    wss
    @12
    @13
    wb
    rinvbij.1
    rinvbij.4b
    cB
    cA
    cF
    funimass3
    mp2an
    mpbi
    @8
    cF
    cA
    rinvbij.2
    imaeq1i
    sseqtri
    eqssi
    @0
    cB
    cA
    @1
    f1oeq3
    ax-mp
    mpbi
end
