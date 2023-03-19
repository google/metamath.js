include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cdif.mm"
include "ciun.mm"
include "cint.mm"
include "ciin.mm"
include "iundif2.mm"
include "intiin.mm"
include "difeq2i.mm"
include "eqtr4i.mm"
include "wss.mm"
include "wceq.mm"
include "cpw.mm"
include "wa.mm"
include "cuni.mm"
include "jctl.mm"
include "intssuni2.mm"
include "unipw.mm"
include "sseq2i.mm"
include "biimpi.mm"
include "3syl.mm"
include "dfss4.mm"
include "sylib.mm"
include "syl5req.mm"

theorem iundifdif
  let vx: setvar x
  let cA: class A
  let cO: class O
  assume iundifdif.o: |- O e. _V
  assume iundifdif.2: |- A C_ ~P O

  disjoint A x
  disjoint O x
  assert |- ( A =/= (/) -> |^| A = ( O \ U_ x e. A ( O \ x ) ) )

  proof
    cA
    c0
    wne
    #
    cO
    vx
    cA
    cO
    vx
    cv
    #
    cdif
    ciun
    #
    cdif
    cO
    cO
    cA
    cint
    #
    cdif
    #
    cdif
    #
    @3
    @2
    @4
    cO
    @2
    cO
    vx
    cA
    @1
    ciin
    #
    cdif
    @4
    vx
    cA
    cO
    @1
    iundif2
    @3
    @6
    cO
    vx
    cA
    intiin
    difeq2i
    eqtr4i
    difeq2i
    @0
    @3
    cO
    wss
    #
    @5
    @3
    wceq
    @0
    cA
    cO
    cpw
    #
    wss
    #
    @0
    wa
    @3
    @8
    cuni
    #
    wss
    #
    @7
    @0
    @9
    iundifdif.2
    jctl
    cA
    @8
    intssuni2
    @11
    @7
    @10
    cO
    @3
    cO
    unipw
    sseq2i
    biimpi
    3syl
    @3
    cO
    dfss4
    sylib
    syl5req
end
