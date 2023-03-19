include "c0.mm"
include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "wrd0.mm"
include "ccatlid.mm"
include "ax-mp.mm"

theorem ccatidid



  assert |- ( (/) ++ (/) ) = (/)

  proof
    c0
    cvv
    cword
    wcel
    c0
    c0
    cconcat
    co
    c0
    wceq
    cvv
    wrd0
    cvv
    c0
    ccatlid
    ax-mp
end
