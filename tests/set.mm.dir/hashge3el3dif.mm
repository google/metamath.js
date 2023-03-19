include "wcel.mm"
include "c3.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "wrex.mm"
include "c0.mm"
include "csn.mm"
include "ctp.mm"
include "cdom.mm"
include "wceq.mm"
include "0nep0.mm"
include "0ex.mm"
include "sneqr.mm"
include "necon3i.mm"
include "ax-mp.mm"
include "cvv.mm"
include "snex.mm"
include "snnzg.mm"
include "3pm3.2i.mm"
include "wb.mm"
include "hashtpg.mm"
include "mpbi.mm"
include "eqcomi.mm"
include "a1i.mm"
include "breq1d.mm"
include "cfn.mm"
include "tpfi.mm"
include "hashdom.mm"
include "mpan.mm"
include "bitrd.mm"
include "wf1.mm"
include "wex.mm"
include "brdomg.mm"
include "wi.mm"
include "wa.mm"
include "necomd.mm"
include "simpr.mm"
include "f1dom3el3dif.mm"
include "expcom.mm"
include "exlimiv.mm"
include "com12.mm"
include "sylbid.mm"
include "imp.mm"

theorem hashge3el3dif
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cD: class D
  let cV: class V
  let vf: setvar f

  disjoint D x
  disjoint D y
  disjoint D z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D f
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint V f
  assert |- ( ( D e. V /\ 3 <_ ( # ` D ) ) -> E. x e. D E. y e. D E. z e. D ( x =/= y /\ x =/= z /\ y =/= z ) )

  proof
    cD
    cV
    wcel
    #
    c3
    cD
    chash
    cfv
    #
    cle
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    wne
    @3
    vz
    cv
    #
    wne
    @4
    @5
    wne
    w3a
    vz
    cD
    wrex
    vy
    cD
    wrex
    vx
    cD
    wrex
    #
    @0
    @2
    c0
    c0
    csn
    #
    @7
    csn
    #
    ctp
    #
    cD
    cdom
    wbr
    #
    @6
    @0
    @2
    @9
    chash
    cfv
    #
    @1
    cle
    wbr
    #
    @10
    @0
    c3
    @11
    @1
    cle
    c3
    @11
    wceq
    @0
    @11
    c3
    c0
    @7
    wne
    #
    @7
    @8
    wne
    #
    @8
    c0
    wne
    #
    w3a
    #
    @11
    c3
    wceq
    #
    @13
    @14
    @15
    0nep0
    @13
    @14
    0nep0
    @7
    @8
    c0
    @7
    c0
    @7
    0ex
    sneqr
    necon3i
    ax-mp
    #
    @7
    cvv
    wcel
    #
    @15
    c0
    snex
    #
    @7
    cvv
    snnzg
    #
    ax-mp
    3pm3.2i
    c0
    cvv
    wcel
    #
    @19
    @8
    cvv
    wcel
    #
    w3a
    #
    @16
    @17
    wb
    @22
    @19
    @23
    0ex
    @20
    @7
    snex
    3pm3.2i
    #
    c0
    @7
    @8
    cvv
    cvv
    cvv
    hashtpg
    ax-mp
    mpbi
    eqcomi
    a1i
    breq1d
    @9
    cfn
    wcel
    @0
    @12
    @10
    wb
    c0
    @7
    @8
    tpfi
    @9
    cD
    cV
    hashdom
    mpan
    bitrd
    @0
    @10
    @9
    cD
    vf
    cv
    #
    wf1
    #
    vf
    wex
    #
    @6
    @9
    cD
    cV
    vf
    brdomg
    @28
    @0
    @6
    @27
    @0
    @6
    wi
    vf
    @0
    @27
    @6
    @0
    @27
    wa
    #
    vx
    vy
    vz
    c0
    @7
    @8
    cD
    @26
    cvv
    cvv
    cvv
    @24
    @29
    @25
    a1i
    @13
    c0
    @8
    wne
    #
    @14
    w3a
    @29
    @13
    @30
    @14
    0nep0
    @19
    @30
    @20
    @19
    @8
    c0
    @21
    necomd
    ax-mp
    @18
    3pm3.2i
    a1i
    @0
    @27
    simpr
    f1dom3el3dif
    expcom
    exlimiv
    com12
    sylbid
    sylbid
    imp
end
