include "cxr.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "csup.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wral.mm"
include "cle.mm"
include "wrex.mm"
include "supxrlub.mm"
include "notbid.mm"
include "ralnex.mm"
include "syl6bbr.mm"
include "wb.mm"
include "supxrcl.mm"
include "xrlenlt.mm"
include "sylan.mm"
include "simpl.mm"
include "sselda.mm"
include "simplr.mm"
include "syl2anc.mm"
include "ralbidva.mm"
include "3bitr4d.mm"

theorem supxrleub
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B y
  disjoint B z
  disjoint B w
  assert |- ( ( A C_ RR* /\ B e. RR* ) -> ( sup ( A , RR* , < ) <_ B <-> A. x e. A x <_ B ) )

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
    cB
    cA
    cxr
    clt
    csup
    #
    clt
    wbr
    #
    wn
    #
    cB
    vx
    cv
    #
    clt
    wbr
    #
    wn
    #
    vx
    cA
    wral
    #
    @3
    cB
    cle
    wbr
    #
    @6
    cB
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
    vx
    cA
    cB
    supxrlub
    notbid
    @7
    vx
    cA
    ralnex
    syl6bbr
    @0
    @3
    cxr
    wcel
    @1
    @10
    @5
    wb
    cA
    supxrcl
    @3
    cB
    xrlenlt
    sylan
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
    @6
    cxr
    wcel
    @1
    @11
    @8
    wb
    @2
    cA
    cxr
    @6
    @0
    @1
    simpl
    sselda
    @0
    @1
    @13
    simplr
    @6
    cB
    xrlenlt
    syl2anc
    ralbidva
    3bitr4d
end
