include "cxr.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "cinf.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wral.mm"
include "cle.mm"
include "wrex.mm"
include "wor.mm"
include "xrltso.mm"
include "a1i.mm"
include "xrinfmss.mm"
include "id.mm"
include "infglbb.mm"
include "notbid.mm"
include "ralnex.mm"
include "syl6bbr.mm"
include "wb.mm"
include "infxrcl.mm"
include "xrlenlt.mm"
include "syl2anr.mm"
include "simplr.mm"
include "simpl.mm"
include "sselda.mm"
include "xrlenltd.mm"
include "ralbidva.mm"
include "3bitr4d.mm"

theorem infxrgelb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z

  disjoint B x
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( ( A C_ RR* /\ B e. RR* ) -> ( B <_ inf ( A , RR* , < ) <-> A. x e. A B <_ x ) )

  proof
    cA
    cxr
    wss
    #
    cB
    cxr
    wcel
    #
    wa
    #
    cA
    cxr
    clt
    cinf
    #
    cB
    clt
    wbr
    #
    wn
    #
    vx
    cv
    #
    cB
    clt
    wbr
    #
    wn
    #
    vx
    cA
    wral
    #
    cB
    @3
    cle
    wbr
    #
    cB
    @6
    cle
    wbr
    #
    vx
    cA
    wral
    @2
    @5
    @7
    vx
    cA
    wrex
    #
    wn
    @9
    @2
    @4
    @12
    @0
    vz
    vy
    vx
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
    vz
    vy
    vx
    cA
    xrinfmss
    @0
    id
    infglbb
    notbid
    @7
    vx
    cA
    ralnex
    syl6bbr
    @1
    @1
    @3
    cxr
    wcel
    @10
    @5
    wb
    @0
    @1
    id
    cA
    infxrcl
    cB
    @3
    xrlenlt
    syl2anr
    @2
    @11
    @8
    vx
    cA
    @2
    @6
    cA
    wcel
    #
    wa
    cB
    @6
    @0
    @1
    @13
    simplr
    @2
    cA
    cxr
    @6
    @0
    @1
    simpl
    sselda
    xrlenltd
    ralbidva
    3bitr4d
end
