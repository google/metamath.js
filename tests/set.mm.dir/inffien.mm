include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "cfi.mm"
include "cfv.mm"
include "cen.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cint.mm"
include "cmpt.mm"
include "wfo.mm"
include "cvv.mm"
include "wss.mm"
include "infpwfien.mm"
include "relen.mm"
include "brrelexi.mm"
include "syl.mm"
include "difss.mm"
include "ssdomg.mm"
include "mpisyl.mm"
include "domentr.mm"
include "syl2anc.mm"
include "numdom.mm"
include "syldan.mm"
include "eqid.mm"
include "fifo.mm"
include "adantr.mm"
include "fodomnum.mm"
include "sylc.mm"
include "domtr.mm"
include "fvex.mm"
include "ssfii.mm"
include "mpsyl.mm"
include "sbth.mm"

theorem inffien
  let cA: class A
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. dom card /\ _om ~<_ A ) -> ( fi ` A ) ~~ A )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    com
    cA
    cdom
    wbr
    #
    wa
    #
    cA
    cfi
    cfv
    #
    cA
    cdom
    wbr
    #
    cA
    @4
    cdom
    wbr
    #
    @4
    cA
    cen
    wbr
    @3
    @4
    cA
    cpw
    cfn
    cin
    #
    c0
    csn
    #
    cdif
    #
    cdom
    wbr
    #
    @9
    cA
    cdom
    wbr
    #
    @5
    @3
    @9
    @0
    wcel
    #
    @9
    @4
    vx
    @9
    vx
    cv
    cint
    cmpt
    #
    wfo
    #
    @10
    @1
    @2
    @11
    @12
    @3
    @9
    @7
    cdom
    wbr
    #
    @7
    cA
    cen
    wbr
    #
    @11
    @3
    @7
    cvv
    wcel
    #
    @9
    @7
    wss
    @15
    @3
    @16
    @17
    cA
    infpwfien
    #
    @7
    cA
    cen
    relen
    brrelexi
    syl
    @7
    @8
    difss
    @9
    @7
    cvv
    ssdomg
    mpisyl
    @18
    @9
    @7
    cA
    domentr
    syl2anc
    #
    cA
    @9
    numdom
    syldan
    @1
    @14
    @2
    vx
    cA
    @13
    @0
    @13
    eqid
    fifo
    adantr
    @9
    @4
    @13
    fodomnum
    sylc
    @19
    @4
    @9
    cA
    domtr
    syl2anc
    @4
    cvv
    wcel
    @3
    cA
    @4
    wss
    #
    @6
    cA
    cfi
    fvex
    @1
    @20
    @2
    cA
    @0
    ssfii
    adantr
    cA
    @4
    cvv
    ssdomg
    mpsyl
    @4
    cA
    sbth
    syl2anc
end
