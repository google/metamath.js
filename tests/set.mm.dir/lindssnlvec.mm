include "clvec.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "c0g.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "csca.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "clininds.mm"
include "wbr.mm"
include "wa.mm"
include "eldifsni.mm"
include "adantl.mm"
include "simpl3.mm"
include "eqid.mm"
include "simpl1.mm"
include "eldifi.mm"
include "simpl2.mm"
include "lvecvsn0.mm"
include "mpbir2and.mm"
include "ralrimiva.mm"
include "clmod.mm"
include "wb.mm"
include "lveclmod.mm"
include "anim1i.mm"
include "3adant3.mm"
include "snlindsntor.mm"
include "syl.mm"
include "mpbid.mm"

theorem lindssnlvec
  let cS: class S
  let cM: class M
  let vs: setvar s
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( M e. LVec /\ S e. ( Base ` M ) /\ S =/= ( 0g ` M ) ) -> { S } linIndS M )

  proof
    cM
    clvec
    wcel
    #
    cS
    cM
    cbs
    cfv
    #
    wcel
    #
    cS
    cM
    c0g
    cfv
    #
    wne
    #
    w3a
    #
    vs
    cv
    #
    cS
    cM
    cvsca
    cfv
    #
    co
    @3
    wne
    #
    vs
    cM
    csca
    cfv
    #
    cbs
    cfv
    #
    @9
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    cS
    csn
    cM
    clininds
    wbr
    #
    @5
    @8
    vs
    @13
    @5
    @6
    @13
    wcel
    #
    wa
    #
    @8
    @6
    @11
    wne
    #
    @4
    @16
    @18
    @5
    @6
    @10
    @11
    eldifsni
    adantl
    @0
    @2
    @4
    @16
    simpl3
    @17
    @6
    @7
    @9
    @10
    @11
    @1
    cM
    cS
    @3
    @1
    eqid
    #
    @7
    eqid
    #
    @9
    eqid
    #
    @10
    eqid
    #
    @11
    eqid
    #
    @3
    eqid
    #
    @0
    @2
    @4
    @16
    simpl1
    @16
    @6
    @10
    wcel
    @5
    @6
    @10
    @12
    eldifi
    adantl
    @0
    @2
    @4
    @16
    simpl2
    lvecvsn0
    mpbir2and
    ralrimiva
    @5
    cM
    clmod
    wcel
    #
    @2
    wa
    #
    @14
    @15
    wb
    @0
    @2
    @26
    @4
    @0
    @25
    @2
    cM
    lveclmod
    anim1i
    3adant3
    @1
    @9
    @10
    @7
    cM
    cS
    @11
    @3
    vs
    @19
    @21
    @22
    @23
    @24
    @20
    snlindsntor
    syl
    mpbid
end
