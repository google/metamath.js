include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "eqid.mm"
include "erngbase-rN.mm"
include "eqcomd.mm"
include "cplusg.mm"
include "cv.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "erngfplus-rN.mm"
include "syl6reqr.mm"
include "erngdvlem1-rN.mm"
include "tendoplcom.mm"
include "isabld.mm"

theorem erngdvlem2-rN
  let cB: class B
  let cD: class D
  let cP: class P
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let cO: class O
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  assume ernggrp.h-r: |- H = ( LHyp ` K )
  assume ernggrp.d-r: |- D = ( ( EDRingR ` K ) ` W )
  assume ernggrplem.b-r: |- B = ( Base ` K )
  assume ernggrplem.t-r: |- T = ( ( LTrn ` K ) ` W )
  assume ernggrplem.e-r: |- E = ( ( TEndo ` K ) ` W )
  assume ernggrplem.p-r: |- P = ( a e. E , b e. E |-> ( f e. T |-> ( ( a ` f ) o. ( b ` f ) ) ) )
  assume ernggrplem.o-r: |- O = ( f e. T |-> ( _I |` B ) )
  assume ernggrplem.i-r: |- I = ( a e. E |-> ( f e. T |-> `' ( a ` f ) ) )

  disjoint B f
  disjoint a b
  disjoint E a
  disjoint E b
  disjoint a f
  disjoint K a
  disjoint b f
  disjoint K b
  disjoint K f
  disjoint H f
  disjoint T a
  disjoint T b
  disjoint T f
  disjoint W a
  disjoint W b
  disjoint W f
  disjoint s t
  disjoint s u
  disjoint D s
  disjoint t u
  disjoint D t
  disjoint D u
  disjoint a s
  disjoint a t
  disjoint a u
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint E s
  disjoint E t
  disjoint E u
  disjoint I t
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint K s
  disjoint K t
  disjoint K u
  disjoint H s
  disjoint H t
  disjoint H u
  disjoint O s
  disjoint O t
  disjoint O u
  disjoint T s
  disjoint W s
  disjoint W t
  disjoint W u
  disjoint P s
  disjoint P t
  disjoint P u
  assert |- ( ( K e. HL /\ W e. H ) -> D e. Abel )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    vs
    vt
    cE
    cP
    cD
    @0
    cD
    cbs
    cfv
    #
    cE
    @1
    cD
    cT
    cE
    cH
    cK
    chlt
    cW
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @1
    eqid
    erngbase-rN
    eqcomd
    @0
    cD
    cplusg
    cfv
    #
    va
    vb
    cE
    cE
    vf
    cT
    vf
    cv
    #
    va
    cv
    cfv
    @3
    vb
    cv
    cfv
    ccom
    cmpt
    cmpt2
    cP
    vb
    cD
    @2
    cT
    vf
    cE
    cH
    cK
    chlt
    cW
    va
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrp.d-r
    @2
    eqid
    erngfplus-rN
    ernggrplem.p-r
    syl6reqr
    cB
    cD
    cP
    cT
    vf
    cE
    cH
    cI
    cK
    cO
    cW
    va
    vb
    ernggrp.h-r
    ernggrp.d-r
    ernggrplem.b-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.p-r
    ernggrplem.o-r
    ernggrplem.i-r
    erngdvlem1-rN
    vb
    cP
    cT
    vs
    cv
    vf
    cE
    cH
    cK
    vt
    cv
    cW
    va
    ernggrp.h-r
    ernggrplem.t-r
    ernggrplem.e-r
    ernggrplem.p-r
    tendoplcom
    isabld
end
