include "clmod.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cfrlm.mm"
include "co.mm"
include "clmic.mm"
include "wbr.mm"
include "wex.mm"
include "n0.mm"
include "wa.mm"
include "cen.mm"
include "vex.mm"
include "enref.mm"
include "lbslcic.mm"
include "mp3an3.mm"
include "weq.mm"
include "oveq2.mm"
include "breq2d.mm"
include "spcev.mm"
include "syl.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "clbs.mm"
include "cfv.mm"
include "lmicsym.mm"
include "lmiclcl.mm"
include "cuvc.mm"
include "crn.mm"
include "crg.mm"
include "cvv.mm"
include "lmodring.mm"
include "eqid.mm"
include "frlmlbs.mm"
include "sylancl.mm"
include "ne0i.mm"
include "lmiclbs.mm"
include "sylc.mm"
include "exlimiv.mm"
include "impbid1.mm"

theorem lmisfree
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cW: class W
  let vj: setvar j
  assume lmisfree.j: |- J = ( LBasis ` W )
  assume lmisfree.f: |- F = ( Scalar ` W )

  disjoint F k
  disjoint J k
  disjoint W k
  disjoint F j
  disjoint j k
  disjoint J j
  disjoint W j
  assert |- ( W e. LMod -> ( J =/= (/) <-> E. k W ~=m ( F freeLMod k ) ) )

  proof
    cW
    clmod
    wcel
    #
    cJ
    c0
    wne
    #
    cW
    cF
    vk
    cv
    #
    cfrlm
    co
    #
    clmic
    wbr
    #
    vk
    wex
    #
    @1
    vj
    cv
    #
    cJ
    wcel
    #
    vj
    wex
    @0
    @5
    vj
    cJ
    n0
    @0
    @7
    @5
    vj
    @0
    @7
    @5
    @0
    @7
    wa
    cW
    cF
    @6
    cfrlm
    co
    #
    clmic
    wbr
    #
    @5
    @0
    @7
    @6
    @6
    cen
    wbr
    @9
    @6
    vj
    vex
    #
    enref
    @6
    cF
    @6
    cJ
    cW
    lmisfree.f
    lmisfree.j
    lbslcic
    mp3an3
    @4
    @9
    vk
    @6
    @10
    vk
    vj
    weq
    @3
    @8
    cW
    clmic
    @2
    @6
    cF
    cfrlm
    oveq2
    breq2d
    spcev
    syl
    ex
    exlimdv
    syl5bi
    @4
    @1
    vk
    @4
    @3
    cW
    clmic
    wbr
    @3
    clbs
    cfv
    #
    c0
    wne
    #
    @1
    cW
    @3
    lmicsym
    @4
    @0
    @12
    cW
    @3
    lmiclcl
    @0
    cF
    @2
    cuvc
    co
    #
    crn
    #
    @11
    wcel
    #
    @12
    @0
    cF
    crg
    wcel
    @2
    cvv
    wcel
    @15
    cF
    cW
    lmisfree.f
    lmodring
    vk
    vex
    cF
    @13
    @3
    @2
    @11
    cvv
    @3
    eqid
    @13
    eqid
    @11
    eqid
    #
    frlmlbs
    sylancl
    @11
    @14
    ne0i
    syl
    syl
    @3
    cW
    @11
    cJ
    @16
    lmisfree.j
    lmiclbs
    sylc
    exlimiv
    impbid1
end
