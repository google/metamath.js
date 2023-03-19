include "cmnc.mm"
include "cfv.mm"
include "wcel.mm"
include "cdgr.mm"
include "ccoe.mm"
include "c1.mm"
include "wceq.mm"
include "c0p.mm"
include "wne.mm"
include "mnccoe.mm"
include "cc0.mm"
include "cn0.mm"
include "csn.mm"
include "cxp.mm"
include "coe0.mm"
include "fveq1i.mm"
include "dgr0.mm"
include "0nn0.mm"
include "eqeltri.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "0ne1.mm"
include "eqnetri.mm"
include "fveq2.mm"
include "fveq12d.mm"
include "neeq1d.mm"
include "mpbiri.mm"
include "necon2i.mm"
include "syl.mm"

theorem mncn0
  let cP: class P
  let cS: class S
  let vs: setvar s
  let vp: setvar p


  assert |- ( P e. ( Monic ` S ) -> P =/= 0p )

  proof
    cP
    cS
    cmnc
    cfv
    wcel
    cP
    cdgr
    cfv
    #
    cP
    ccoe
    cfv
    #
    cfv
    #
    c1
    wceq
    cP
    c0p
    wne
    cP
    cS
    mnccoe
    cP
    c0p
    @2
    c1
    cP
    c0p
    wceq
    #
    @2
    c1
    wne
    c0p
    cdgr
    cfv
    #
    c0p
    ccoe
    cfv
    #
    cfv
    #
    c1
    wne
    @6
    cc0
    c1
    @6
    @4
    cn0
    cc0
    csn
    cxp
    #
    cfv
    #
    cc0
    @4
    @5
    @7
    coe0
    fveq1i
    @4
    cn0
    wcel
    @8
    cc0
    wceq
    @4
    cc0
    cn0
    dgr0
    0nn0
    eqeltri
    cn0
    cc0
    @4
    c0ex
    fvconst2
    ax-mp
    eqtri
    0ne1
    eqnetri
    @3
    @2
    @6
    c1
    @3
    @0
    @4
    @1
    @5
    cP
    c0p
    ccoe
    fveq2
    cP
    c0p
    cdgr
    fveq2
    fveq12d
    neeq1d
    mpbiri
    necon2i
    syl
end
