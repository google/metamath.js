include "cxr.mm"
include "wss.mm"
include "cmnf.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wa.mm"
include "cun.mm"
include "ssdifss.mm"
include "supxrmnf.mm"
include "syl.mm"
include "adantr.mm"
include "difsnid.mm"
include "supeq1d.mm"
include "adantl.mm"
include "eqtr3d.mm"
include "wn.mm"
include "difsn.mm"
include "pm2.61dan.mm"

theorem supxrmnf2
  let cA: class A


  assert |- ( A C_ RR* -> sup ( ( A \ { -oo } ) , RR* , < ) = sup ( A , RR* , < ) )

  proof
    cA
    cxr
    wss
    #
    cmnf
    cA
    wcel
    #
    cA
    cmnf
    csn
    #
    cdif
    #
    cxr
    clt
    csup
    #
    cA
    cxr
    clt
    csup
    #
    wceq
    #
    @0
    @1
    wa
    @3
    @2
    cun
    #
    cxr
    clt
    csup
    #
    @4
    @5
    @0
    @8
    @4
    wceq
    #
    @1
    @0
    @3
    cxr
    wss
    @9
    cA
    cxr
    @2
    ssdifss
    @3
    supxrmnf
    syl
    adantr
    @1
    @8
    @5
    wceq
    @0
    @1
    cxr
    @7
    cA
    clt
    cA
    cmnf
    difsnid
    supeq1d
    adantl
    eqtr3d
    @1
    wn
    #
    @6
    @0
    @10
    cxr
    @3
    cA
    clt
    cmnf
    cA
    difsn
    supeq1d
    adantl
    pm2.61dan
end
