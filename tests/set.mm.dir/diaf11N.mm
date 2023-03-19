include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "wf1o.mm"
include "cple.mm"
include "wbr.mm"
include "cbs.mm"
include "crab.mm"
include "eqid.mm"
include "diafn.mm"
include "wfun.mm"
include "fnfun.mm"
include "funfn.mm"
include "sylib.mm"
include "syl.mm"
include "eqidd.mm"
include "diaeldm.mm"
include "anbi12d.mm"
include "w3a.mm"
include "dia11N.mm"
include "biimpd.mm"
include "3expib.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "dff1o6.mm"
include "syl3anbrc.mm"

theorem diaf11N
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume dia1o.h: |- H = ( LHyp ` K )
  assume dia1o.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> I : dom I -1-1-onto-> ran I )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cI
    cI
    cdm
    #
    wfn
    #
    cI
    crn
    #
    @3
    wceq
    vx
    cv
    #
    cI
    cfv
    vy
    cv
    #
    cI
    cfv
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    @1
    wral
    vx
    @1
    wral
    @1
    @3
    cI
    wf1o
    @0
    cI
    @4
    cW
    cK
    cple
    cfv
    #
    wbr
    #
    vx
    cK
    cbs
    cfv
    #
    crab
    #
    wfn
    #
    @2
    vx
    @11
    cH
    cI
    cK
    @9
    chlt
    cW
    @11
    eqid
    #
    @9
    eqid
    #
    dia1o.h
    dia1o.i
    diafn
    @13
    cI
    wfun
    @2
    @12
    cI
    fnfun
    cI
    funfn
    sylib
    syl
    @0
    @3
    eqidd
    @0
    @8
    vx
    vy
    @1
    @1
    @0
    @4
    @1
    wcel
    #
    @5
    @1
    wcel
    #
    wa
    @4
    @11
    wcel
    @10
    wa
    #
    @5
    @11
    wcel
    @5
    cW
    @9
    wbr
    wa
    #
    wa
    @8
    @0
    @16
    @18
    @17
    @19
    @11
    cH
    cI
    cK
    @9
    chlt
    cW
    @4
    @14
    @15
    dia1o.h
    dia1o.i
    diaeldm
    @11
    cH
    cI
    cK
    @9
    chlt
    cW
    @5
    @14
    @15
    dia1o.h
    dia1o.i
    diaeldm
    anbi12d
    @0
    @18
    @19
    @8
    @0
    @18
    @19
    w3a
    @6
    @7
    @11
    cH
    cI
    cK
    @9
    cW
    @4
    @5
    @14
    @15
    dia1o.h
    dia1o.i
    dia11N
    biimpd
    3expib
    sylbid
    ralrimivv
    vx
    vy
    @1
    @3
    cI
    dff1o6
    syl3anbrc
end
