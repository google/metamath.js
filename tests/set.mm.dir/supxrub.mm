include "cxr.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrsupss.mm"
include "supub.mm"
include "imp.mm"
include "wb.mm"
include "ssel2.mm"
include "supxrcl.mm"
include "adantr.mm"
include "xrlenlt.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem supxrub
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A C_ RR* /\ B e. A ) -> B <_ sup ( A , RR* , < ) )

  proof
    cA
    cxr
    wss
    #
    cB
    cA
    wcel
    #
    wa
    #
    cB
    cA
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    @3
    cB
    clt
    wbr
    wn
    #
    @0
    @1
    @5
    @0
    vx
    vy
    vz
    cxr
    cA
    cB
    clt
    cxr
    clt
    wor
    @0
    xrltso
    a1i
    vx
    vy
    vz
    cA
    xrsupss
    supub
    imp
    @2
    cB
    cxr
    wcel
    @3
    cxr
    wcel
    #
    @4
    @5
    wb
    cA
    cxr
    cB
    ssel2
    @0
    @6
    @1
    cA
    supxrcl
    adantr
    cB
    @3
    xrlenlt
    syl2anc
    mpbird
end
