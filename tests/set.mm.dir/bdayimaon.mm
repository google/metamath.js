include "wcel.mm"
include "cbday.mm"
include "cima.mm"
include "cuni.mm"
include "word.mm"
include "cvv.mm"
include "wa.mm"
include "csuc.mm"
include "con0.mm"
include "wfun.mm"
include "csur.mm"
include "wfo.mm"
include "bdayfo.mm"
include "fofun.mm"
include "ax-mp.mm"
include "funimaexg.mm"
include "mpan.mm"
include "uniexg.mm"
include "syl.mm"
include "wss.mm"
include "crn.mm"
include "imassrn.mm"
include "wceq.mm"
include "forn.mm"
include "sseqtri.mm"
include "ssorduni.mm"
include "jctil.mm"
include "elon2.mm"
include "sucelon.mm"
include "bitr3i.mm"
include "sylib.mm"

theorem bdayimaon
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> suc U. ( bday " A ) e. On )

  proof
    cA
    cV
    wcel
    #
    cbday
    cA
    cima
    #
    cuni
    #
    word
    #
    @2
    cvv
    wcel
    #
    wa
    #
    @2
    csuc
    con0
    wcel
    #
    @0
    @4
    @3
    @0
    @1
    cvv
    wcel
    #
    @4
    cbday
    wfun
    #
    @0
    @7
    csur
    con0
    cbday
    wfo
    #
    @8
    bdayfo
    csur
    con0
    cbday
    fofun
    ax-mp
    cbday
    cA
    cV
    funimaexg
    mpan
    @1
    cvv
    uniexg
    syl
    @1
    con0
    wss
    @3
    @1
    cbday
    crn
    #
    con0
    cbday
    cA
    imassrn
    @9
    @10
    con0
    wceq
    bdayfo
    csur
    con0
    cbday
    forn
    ax-mp
    sseqtri
    @1
    ssorduni
    ax-mp
    jctil
    @5
    @2
    con0
    wcel
    @6
    @2
    elon2
    @2
    sucelon
    bitr3i
    sylib
end
