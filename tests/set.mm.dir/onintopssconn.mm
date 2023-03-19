include "con0.mm"
include "ctop.mm"
include "cin.mm"
include "cconn.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "elin.mm"
include "word.mm"
include "wb.mm"
include "eloni.mm"
include "ordtopconn.mm"
include "syl.mm"
include "biimpa.mm"
include "sylbi.mm"
include "ssriv.mm"

theorem onintopssconn
  let vx: setvar x


  assert |- ( On i^i Top ) C_ Conn

  proof
    vx
    con0
    ctop
    cin
    #
    cconn
    vx
    cv
    #
    @0
    wcel
    @1
    con0
    wcel
    #
    @1
    ctop
    wcel
    #
    wa
    @1
    cconn
    wcel
    #
    @1
    con0
    ctop
    elin
    @2
    @3
    @4
    @2
    @1
    word
    @3
    @4
    wb
    @1
    eloni
    @1
    ordtopconn
    syl
    biimpa
    sylbi
    ssriv
end
