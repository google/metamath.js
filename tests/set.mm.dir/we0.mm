include "c0.mm"
include "wwe.mm"
include "wfr.mm"
include "wor.mm"
include "fr0.mm"
include "so0.mm"
include "df-we.mm"
include "mpbir2an.mm"

theorem we0
  let cR: class R


  assert |- R We (/)

  proof
    c0
    cR
    wwe
    c0
    cR
    wfr
    c0
    cR
    wor
    cR
    fr0
    cR
    so0
    c0
    cR
    df-we
    mpbir2an
end
