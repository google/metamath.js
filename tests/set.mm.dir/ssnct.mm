include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wss.mm"
include "ssct.mm"
include "sylan.mm"
include "wn.mm"
include "adantr.mm"
include "pm2.65da.mm"

theorem ssnct
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume ssnct.1: |- ( ph -> -. A ~<_ _om )
  assume ssnct.2: |- ( ph -> A C_ B )


  assert |- ( ph -> -. B ~<_ _om )

  proof
    wph
    cB
    com
    cdom
    wbr
    #
    cA
    com
    cdom
    wbr
    #
    wph
    cA
    cB
    wss
    @0
    @1
    ssnct.2
    cA
    cB
    ssct
    sylan
    wph
    @1
    wn
    @0
    ssnct.1
    adantr
    pm2.65da
end
