include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "c0v.mm"
include "chsh.mm"
include "sh0.mm"
include "syl.mm"

theorem ch0
  let cH: class H


  assert |- ( H e. CH -> 0h e. H )

  proof
    cH
    cch
    wcel
    cH
    csh
    wcel
    c0v
    cH
    wcel
    cH
    chsh
    cH
    sh0
    syl
end
