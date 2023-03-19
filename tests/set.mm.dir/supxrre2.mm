include "cr.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wcel.mm"
include "cpnf.mm"
include "wbr.mm"
include "supxrre1.mm"
include "wb.mm"
include "wceq.mm"
include "wn.mm"
include "ressxr.mm"
include "sstr.mm"
include "mpan2.mm"
include "supxrcl.mm"
include "nltpnft.mm"
include "3syl.mm"
include "necon2abid.mm"
include "adantr.mm"
include "bitrd.mm"

theorem supxrre2
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B


  assert |- ( ( A C_ RR /\ A =/= (/) ) -> ( sup ( A , RR* , < ) e. RR <-> sup ( A , RR* , < ) =/= +oo ) )

  proof
    cA
    cr
    wss
    #
    cA
    c0
    wne
    #
    wa
    cA
    cxr
    clt
    csup
    #
    cr
    wcel
    @2
    cpnf
    clt
    wbr
    #
    @2
    cpnf
    wne
    #
    cA
    supxrre1
    @0
    @3
    @4
    wb
    @1
    @0
    @3
    @2
    cpnf
    @0
    cA
    cxr
    wss
    #
    @2
    cxr
    wcel
    @2
    cpnf
    wceq
    @3
    wn
    wb
    @0
    cr
    cxr
    wss
    @5
    ressxr
    cA
    cr
    cxr
    sstr
    mpan2
    cA
    supxrcl
    @2
    nltpnft
    3syl
    necon2abid
    adantr
    bitrd
end
