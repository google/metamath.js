include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "chsh.mm"
include "ax-mp.mm"

theorem chshii
  let cH: class H
  assume chshi.1: |- H e. CH


  assert |- H e. SH

  proof
    cH
    cch
    wcel
    cH
    csh
    wcel
    chshi.1
    cH
    chsh
    ax-mp
end
