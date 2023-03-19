include "com.mm"
include "word.mm"
include "con0.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "ordom.mm"
include "ordeleqon.mm"
include "mpbi.mm"

theorem omon



  assert |- ( _om e. On \/ _om = On )

  proof
    com
    word
    com
    con0
    wcel
    com
    con0
    wceq
    wo
    ordom
    com
    ordeleqon
    mpbi
end
