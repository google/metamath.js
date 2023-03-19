include "word.mm"
include "c0.mm"
include "wcel.mm"
include "csuc.mm"
include "wss.mm"
include "c1o.mm"
include "con0.mm"
include "wb.mm"
include "0elon.mm"
include "ordelsuc.mm"
include "mpan.mm"
include "df-1o.mm"
include "sseq1i.mm"
include "syl6bbr.mm"

theorem ordgt0ge1
  let cA: class A


  assert |- ( Ord A -> ( (/) e. A <-> 1o C_ A ) )

  proof
    cA
    word
    #
    c0
    cA
    wcel
    #
    c0
    csuc
    #
    cA
    wss
    #
    c1o
    cA
    wss
    c0
    con0
    wcel
    @0
    @1
    @3
    wb
    0elon
    c0
    cA
    con0
    ordelsuc
    mpan
    c1o
    @2
    cA
    df-1o
    sseq1i
    syl6bbr
end
