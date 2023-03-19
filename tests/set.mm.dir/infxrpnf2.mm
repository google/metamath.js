include "cxr.mm"
include "wss.mm"
include "cpnf.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "wa.mm"
include "cun.mm"
include "ssdifss.mm"
include "infxrpnf.mm"
include "syl.mm"
include "adantr.mm"
include "difsnid.mm"
include "infeq1d.mm"
include "adantl.mm"
include "eqtr3d.mm"
include "wn.mm"
include "difsn.mm"
include "pm2.61dan.mm"

theorem infxrpnf2
  let cA: class A


  assert |- ( A C_ RR* -> inf ( ( A \ { +oo } ) , RR* , < ) = inf ( A , RR* , < ) )

  proof
    cA
    cxr
    wss
    #
    cpnf
    cA
    wcel
    #
    cA
    cpnf
    csn
    #
    cdif
    #
    cxr
    clt
    cinf
    #
    cA
    cxr
    clt
    cinf
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
    cinf
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
    infxrpnf
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
    cpnf
    difsnid
    infeq1d
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
    cpnf
    cA
    difsn
    infeq1d
    adantl
    pm2.61dan
end
