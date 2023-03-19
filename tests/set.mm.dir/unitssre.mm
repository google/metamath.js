include "cc0.mm"
include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wss.mm"
include "0re.mm"
include "1re.mm"
include "iccssre.mm"
include "mp2an.mm"

theorem unitssre



  assert |- ( 0 [,] 1 ) C_ RR

  proof
    cc0
    cr
    wcel
    c1
    cr
    wcel
    cc0
    c1
    cicc
    co
    cr
    wss
    0re
    1re
    cc0
    c1
    iccssre
    mp2an
end
