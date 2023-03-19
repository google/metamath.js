include "c0.mm"
include "csn.mm"
include "ctop.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "ccmp.mm"
include "sn0top.mm"
include "snfi.mm"
include "elin.mm"
include "mpbir2an.mm"
include "fincmp.mm"
include "ax-mp.mm"

theorem 0cmp



  assert |- { (/) } e. Comp

  proof
    c0
    csn
    #
    ctop
    cfn
    cin
    wcel
    #
    @0
    ccmp
    wcel
    @1
    @0
    ctop
    wcel
    @0
    cfn
    wcel
    sn0top
    c0
    snfi
    @0
    ctop
    cfn
    elin
    mpbir2an
    @0
    fincmp
    ax-mp
end
