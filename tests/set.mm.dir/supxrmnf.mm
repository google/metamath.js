include "cxr.mm"
include "wss.mm"
include "cmnf.mm"
include "csn.mm"
include "cun.mm"
include "clt.mm"
include "csup.mm"
include "uncom.mm"
include "supeq1i.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wcel.mm"
include "mnfxr.mm"
include "snssi.mm"
include "mp1i.mm"
include "id.mm"
include "wor.mm"
include "xrltso.mm"
include "supsn.mm"
include "mp2an.mm"
include "supxrcl.mm"
include "mnfle.mm"
include "syl.mm"
include "syl5eqbr.mm"
include "supxrun.mm"
include "syl3anc.mm"
include "syl5eq.mm"

theorem supxrmnf
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B


  assert |- ( A C_ RR* -> sup ( ( A u. { -oo } ) , RR* , < ) = sup ( A , RR* , < ) )

  proof
    cA
    cxr
    wss
    #
    cA
    cmnf
    csn
    #
    cun
    #
    cxr
    clt
    csup
    @1
    cA
    cun
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
    cxr
    @2
    @3
    clt
    cA
    @1
    uncom
    supeq1i
    @0
    @1
    cxr
    wss
    #
    @0
    @1
    cxr
    clt
    csup
    #
    @5
    cle
    wbr
    @4
    @5
    wceq
    cmnf
    cxr
    wcel
    #
    @6
    @0
    mnfxr
    cmnf
    cxr
    snssi
    mp1i
    @0
    id
    @0
    @7
    cmnf
    @5
    cle
    cxr
    clt
    wor
    @8
    @7
    cmnf
    wceq
    xrltso
    mnfxr
    cxr
    cmnf
    clt
    supsn
    mp2an
    @0
    @5
    cxr
    wcel
    cmnf
    @5
    cle
    wbr
    cA
    supxrcl
    @5
    mnfle
    syl
    syl5eqbr
    @1
    cA
    supxrun
    syl3anc
    syl5eq
end
