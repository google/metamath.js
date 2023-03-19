include "c0.mm"
include "c3o.mm"
include "cpw.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "0elpw.mm"
include "cv.mm"
include "csn.mm"
include "c1o.mm"
include "cpr.mm"
include "cif.mm"
include "eqeq1.mm"
include "id.mm"
include "ifbieq2d.mm"
include "wne.mm"
include "0nep0.mm"
include "a1i.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "eqtrd.mm"
include "0ex.mm"
include "fvmpt.mm"
include "ax-mp.mm"

theorem clsk1indlem0
  let cK: class K
  let vr: setvar r
  assume clsk1indlem.k: |- K = ( r e. ~P 3o |-> if ( r = { (/) } , { (/) , 1o } , r ) )


  assert |- ( K ` (/) ) = (/)

  proof
    c0
    c3o
    cpw
    #
    wcel
    c0
    cK
    cfv
    c0
    wceq
    c3o
    0elpw
    vr
    c0
    vr
    cv
    #
    c0
    csn
    #
    wceq
    #
    c0
    c1o
    cpr
    #
    @1
    cif
    #
    c0
    @0
    cK
    @1
    c0
    wceq
    #
    @5
    c0
    @2
    wceq
    #
    @4
    c0
    cif
    c0
    @6
    @3
    @7
    @1
    c0
    @4
    @1
    c0
    @2
    eqeq1
    @6
    id
    ifbieq2d
    @6
    @7
    @4
    c0
    @6
    c0
    @2
    c0
    @2
    wne
    @6
    0nep0
    a1i
    neneqd
    iffalsed
    eqtrd
    clsk1indlem.k
    0ex
    fvmpt
    ax-mp
end
