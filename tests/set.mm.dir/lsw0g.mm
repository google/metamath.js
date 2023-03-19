include "c0.mm"
include "cword.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "clsw.mm"
include "wrd0.mm"
include "hash0.mm"
include "lsw0.mm"
include "mp2an.mm"

theorem lsw0g
  let cV: class V


  assert |- ( lastS ` (/) ) = (/)

  proof
    c0
    cV
    cword
    wcel
    c0
    chash
    cfv
    cc0
    wceq
    c0
    clsw
    cfv
    c0
    wceq
    cV
    wrd0
    hash0
    cV
    c0
    lsw0
    mp2an
end
