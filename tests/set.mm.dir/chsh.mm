include "cch.mm"
include "wcel.mm"
include "csh.mm"
include "chli.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cima.mm"
include "wss.mm"
include "isch.mm"
include "simplbi.mm"

theorem chsh
  let cH: class H


  assert |- ( H e. CH -> H e. SH )

  proof
    cH
    cch
    wcel
    cH
    csh
    wcel
    chli
    cH
    cn
    cmap
    co
    cima
    cH
    wss
    cH
    isch
    simplbi
end
