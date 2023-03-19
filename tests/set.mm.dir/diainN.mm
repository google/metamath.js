include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "ccnv.mm"
include "cfv.mm"
include "co.mm"
include "cin.mm"
include "cdm.mm"
include "wceq.mm"
include "simpl.mm"
include "diacnvclN.mm"
include "adantrr.mm"
include "adantrl.mm"
include "diameetN.mm"
include "syl12anc.mm"
include "wf1o.mm"
include "diaf11N.mm"
include "adantr.mm"
include "simprl.mm"
include "f1ocnvfv2.mm"
include "syl2anc.mm"
include "simprr.mm"
include "ineq12d.mm"
include "eqtr2d.mm"

theorem diainN
  let cH: class H
  let cI: class I
  let cK: class K
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume diam.m: |- ./\ = ( meet ` K )
  assume diam.h: |- H = ( LHyp ` K )
  assume diam.i: |- I = ( ( DIsoA ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. ran I /\ Y e. ran I ) ) -> ( X i^i Y ) = ( I ` ( ( `' I ` X ) ./\ ( `' I ` Y ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cI
    crn
    #
    wcel
    #
    cY
    @1
    wcel
    #
    wa
    #
    wa
    #
    cX
    cI
    ccnv
    #
    cfv
    #
    cY
    @6
    cfv
    #
    c.an
    co
    cI
    cfv
    #
    @7
    cI
    cfv
    #
    @8
    cI
    cfv
    #
    cin
    #
    cX
    cY
    cin
    @5
    @0
    @7
    cI
    cdm
    #
    wcel
    #
    @8
    @13
    wcel
    #
    @9
    @12
    wceq
    @0
    @4
    simpl
    @0
    @2
    @14
    @3
    cH
    cI
    cK
    cW
    cX
    diam.h
    diam.i
    diacnvclN
    adantrr
    @0
    @3
    @15
    @2
    cH
    cI
    cK
    cW
    cY
    diam.h
    diam.i
    diacnvclN
    adantrl
    cH
    cI
    cK
    c.an
    cW
    @7
    @8
    diam.m
    diam.h
    diam.i
    diameetN
    syl12anc
    @5
    @10
    cX
    @11
    cY
    @5
    @13
    @1
    cI
    wf1o
    #
    @2
    @10
    cX
    wceq
    @0
    @16
    @4
    cH
    cI
    cK
    cW
    diam.h
    diam.i
    diaf11N
    adantr
    #
    @0
    @2
    @3
    simprl
    @13
    @1
    cX
    cI
    f1ocnvfv2
    syl2anc
    @5
    @16
    @3
    @11
    cY
    wceq
    @17
    @0
    @2
    @3
    simprr
    @13
    @1
    cY
    cI
    f1ocnvfv2
    syl2anc
    ineq12d
    eqtr2d
end
