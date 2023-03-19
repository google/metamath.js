include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "2cn.mm"
include "2ne0.mm"
include "diveq0.mm"
include "mp3an23.mm"

theorem half0
  let cA: class A


  assert |- ( A e. CC -> ( ( A / 2 ) = 0 <-> A = 0 ) )

  proof
    cA
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    cA
    c2
    cdiv
    co
    cc0
    wceq
    cA
    cc0
    wceq
    wb
    2cn
    2ne0
    cA
    c2
    diveq0
    mp3an23
end
