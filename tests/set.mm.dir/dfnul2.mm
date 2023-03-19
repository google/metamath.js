include "cv.mm"
include "wceq.mm"
include "wn.mm"
include "c0.mm"
include "wcel.mm"
include "cvv.mm"
include "cdif.mm"
include "wa.mm"
include "df-nul.mm"
include "eleq2i.mm"
include "eldif.mm"
include "eqid.mm"
include "pm3.24.mm"
include "2th.mm"
include "con2bii.mm"
include "3bitri.mm"
include "abbi2i.mm"

theorem dfnul2
  let vx: setvar x


  assert |- (/) = { x | -. x = x }

  proof
    vx
    cv
    #
    @0
    wceq
    #
    wn
    #
    vx
    c0
    @0
    c0
    wcel
    @0
    cvv
    cvv
    cdif
    #
    wcel
    @0
    cvv
    wcel
    #
    @4
    wn
    wa
    #
    @2
    c0
    @3
    @0
    df-nul
    eleq2i
    @0
    cvv
    cvv
    eldif
    @1
    @5
    @1
    @5
    wn
    @0
    eqid
    @4
    pm3.24
    2th
    con2bii
    3bitri
    abbi2i
end
