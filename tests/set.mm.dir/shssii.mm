include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "shss.mm"
include "ax-mp.mm"

theorem shssii
  let cH: class H
  assume shssi.1: |- H e. SH


  assert |- H C_ ~H

  proof
    cH
    csh
    wcel
    cH
    chil
    wss
    shssi.1
    cH
    shss
    ax-mp
end
