include "c0.mm"
include "cr.mm"
include "wss.mm"
include "covol.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "0ss.mm"
include "ovol0.mm"
include "nulmbl.mm"
include "mp2an.mm"

theorem 0mbl



  assert |- (/) e. dom vol

  proof
    c0
    cr
    wss
    c0
    covol
    cfv
    cc0
    wceq
    c0
    cvol
    cdm
    wcel
    cr
    0ss
    ovol0
    c0
    nulmbl
    mp2an
end
