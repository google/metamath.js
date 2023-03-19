include "c0.mm"
include "wf.mm"
include "cword.mm"
include "wcel.mm"
include "f0.mm"
include "iswrddm0.mm"
include "ax-mp.mm"

theorem wrd0
  let cS: class S


  assert |- (/) e. Word S

  proof
    c0
    cS
    c0
    wf
    c0
    cS
    cword
    wcel
    cS
    f0
    cS
    c0
    iswrddm0
    ax-mp
end
