include "cword.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cc0.mm"
include "ccsh.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "wf.mm"
include "cshwcl.mm"
include "wrdf.mm"
include "syl.mm"
include "adantr.mm"
include "cshwlen.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "mpbid.mm"

theorem cshwf
  let cA: class A
  let cN: class N
  let cW: class W


  assert |- ( ( W e. Word A /\ N e. ZZ ) -> ( W cyclShift N ) : ( 0 ..^ ( # ` W ) ) --> A )

  proof
    cW
    cA
    cword
    #
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cc0
    cW
    cN
    ccsh
    co
    #
    chash
    cfv
    #
    cfzo
    co
    #
    cA
    @4
    wf
    #
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cA
    @4
    wf
    @1
    @7
    @2
    @1
    @4
    @0
    wcel
    @7
    cN
    cA
    cW
    cshwcl
    cA
    @4
    wrdf
    syl
    adantr
    @3
    @6
    @9
    cA
    @4
    @3
    @5
    @8
    cc0
    cfzo
    cN
    cA
    cW
    cshwlen
    oveq2d
    feq2d
    mpbid
end
