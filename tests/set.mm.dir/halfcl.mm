include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "2cn.mm"
include "2ne0.mm"
include "divcl.mm"
include "mp3an23.mm"

theorem halfcl
  let cA: class A


  assert |- ( A e. CC -> ( A / 2 ) e. CC )

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
    cc
    wcel
    2cn
    2ne0
    cA
    c2
    divcl
    mp3an23
end
