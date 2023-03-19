include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cint.mm"
include "cv.mm"
include "cdif.mm"
include "ciun.mm"
include "wceq.mm"
include "wa.mm"
include "ciin.mm"
include "iundif2.mm"
include "intiin.mm"
include "difeq2i.mm"
include "eqtr4i.mm"
include "cuni.mm"
include "intssuni2.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "dfss4.mm"
include "sylib.mm"
include "syl5req.mm"
include "ex.mm"

theorem iundifdifd
  let vx: setvar x
  let cA: class A
  let cO: class O

  disjoint A x
  disjoint O x
  assert |- ( A C_ ~P O -> ( A =/= (/) -> |^| A = ( O \ U_ x e. A ( O \ x ) ) ) )

  proof
    cA
    cO
    cpw
    #
    wss
    #
    cA
    c0
    wne
    #
    cA
    cint
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
    #
    wceq
    @1
    @2
    wa
    #
    @6
    cO
    cO
    @3
    cdif
    #
    cdif
    #
    @3
    @5
    @8
    cO
    @5
    cO
    vx
    cA
    @4
    ciin
    #
    cdif
    @8
    vx
    cA
    cO
    @4
    iundif2
    @3
    @10
    cO
    vx
    cA
    intiin
    difeq2i
    eqtr4i
    difeq2i
    @7
    @3
    cO
    wss
    @9
    @3
    wceq
    @7
    @3
    @0
    cuni
    cO
    cA
    @0
    intssuni2
    cO
    unipw
    syl6sseq
    @3
    cO
    dfss4
    sylib
    syl5req
    ex
end
