include "cr.mm"
include "wcel.mm"
include "c2.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "2re.mm"
include "2ne0.mm"
include "redivcl.mm"
include "mp3an23.mm"

theorem rehalfcl
  let cA: class A


  assert |- ( A e. RR -> ( A / 2 ) e. RR )

  proof
    cA
    cr
    wcel
    c2
    cr
    wcel
    c2
    cc0
    wne
    cA
    c2
    cdiv
    co
    cr
    wcel
    2re
    2ne0
    cA
    c2
    redivcl
    mp3an23
end
