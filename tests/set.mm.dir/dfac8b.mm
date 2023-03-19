include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wwe.mm"
include "cen.mm"
include "wbr.mm"
include "cardid2.mm"
include "bren.mm"
include "sylib.mm"
include "ccnv.mm"
include "cep.mm"
include "copab.mm"
include "cxp.mm"
include "cin.mm"
include "cvv.mm"
include "sqxpexg.mm"
include "incom.mm"
include "inex1g.mm"
include "syl5eqel.mm"
include "syl.mm"
include "f1ocnv.mm"
include "word.mm"
include "cardon.mm"
include "onordi.mm"
include "ordwe.mm"
include "ax-mp.mm"
include "eqid.mm"
include "f1owe.mm"
include "mpisyl.mm"
include "weinxp.mm"
include "weeq1.mm"
include "spcegv.mm"
include "syl2im.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem dfac8b
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z

  disjoint A x
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint A f
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A z
  assert |- ( A e. dom card -> E. x x We A )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cA
    ccrd
    cfv
    #
    cA
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    cA
    vx
    cv
    #
    wwe
    #
    vx
    wex
    #
    @1
    @2
    cA
    cen
    wbr
    @5
    cA
    cardid2
    @2
    cA
    vf
    bren
    sylib
    @1
    @4
    @8
    vf
    @1
    vz
    cv
    @3
    ccnv
    #
    cfv
    vw
    cv
    @9
    cfv
    cep
    wbr
    vz
    vw
    copab
    #
    cA
    cA
    cxp
    #
    cin
    #
    cvv
    wcel
    #
    @4
    cA
    @12
    wwe
    #
    @8
    @1
    @11
    cvv
    wcel
    #
    @13
    cA
    @0
    sqxpexg
    @15
    @12
    @11
    @10
    cin
    cvv
    @10
    @11
    incom
    @11
    @10
    cvv
    inex1g
    syl5eqel
    syl
    @4
    cA
    @10
    wwe
    #
    @14
    @4
    cA
    @2
    @9
    wf1o
    @2
    cep
    wwe
    #
    @16
    @2
    cA
    @3
    f1ocnv
    @2
    word
    @17
    @2
    cA
    cardon
    onordi
    @2
    ordwe
    ax-mp
    vz
    vw
    cA
    @2
    @10
    cep
    @9
    @10
    eqid
    f1owe
    mpisyl
    cA
    @10
    weinxp
    sylib
    @7
    @14
    vx
    @12
    cvv
    cA
    @6
    @12
    weeq1
    spcegv
    syl2im
    exlimdv
    mpd
end
