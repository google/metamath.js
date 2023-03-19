include "cz.mm"
include "wcel.mm"
include "csn.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfzo.mm"
include "snidg.mm"
include "fzosn.mm"
include "eleqtrrd.mm"

theorem elfzomin
  let cZ: class Z


  assert |- ( Z e. ZZ -> Z e. ( Z ..^ ( Z + 1 ) ) )

  proof
    cZ
    cz
    wcel
    cZ
    cZ
    csn
    cZ
    cZ
    c1
    caddc
    co
    cfzo
    co
    cZ
    cz
    snidg
    cZ
    fzosn
    eleqtrrd
end
