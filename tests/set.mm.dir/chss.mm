include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "chil.mm"
include "wss.mm"
include "chsh.mm"
include "shss.mm"
include "syl.mm"

theorem chss
  let cH: class H


  assert |- ( H e. CH -> H C_ ~H )

  proof
    cH
    cch
    wcel
    cH
    csh
    wcel
    cH
    chil
    wss
    cH
    chsh
    cH
    shss
    syl
end
