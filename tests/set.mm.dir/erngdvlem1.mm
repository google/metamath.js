include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cbs.mm"
include "eqid.mm"
include "erngbase.mm"
include "eqcomd.mm"
include "cplusg.mm"
include "ccom.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "erngfplus.mm"
include "syl6reqr.mm"
include "tendoplcl.mm"
include "tendoplass.mm"
include "tendo0cl.mm"
include "tendo0pl.mm"
include "tendoicl.mm"
include "tendoipl.mm"
include "isgrpd.mm"

theorem erngdvlem1
  let cB: class B
  let cD: class D
  let cP: class P
  let cT: class T
  let vf: setvar f
  let cE: class E
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  assume ernggrp.h: |- H = ( LHyp ` K )
  assume ernggrp.d: |- D = ( ( EDRing ` K ) ` W )
  assume erngdv.b: |- B = ( Base ` K )
  assume erngdv.t: |- T = ( ( LTrn ` K ) ` W )
  assume erngdv.e: |- E = ( ( TEndo ` K ) ` W )
  assume erngdv.p: |- P = ( a e. E , b e. E |-> ( f e. T |-> ( ( a ` f ) o. ( b ` f ) ) ) )
  assume erngdv.o: |- .0. = ( f e. T |-> ( _I |` B ) )
  assume erngdv.i: |- I = ( a e. E |-> ( f e. T |-> `' ( a ` f ) ) )

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
  disjoint .0. s
  disjoint .0. t
  disjoint .0. u
  disjoint T s
  disjoint W s
  disjoint W t
  disjoint W u
  disjoint P s
  disjoint P t
  disjoint P u
  assert |- ( ( K e. HL /\ W e. H ) -> D e. Grp )

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
    vu
    cE
    cP
    cD
    vs
    cv
    #
    cI
    cfv
    c.0
    @0
    cD
    cbs
    cfv
    #
    cE
    @2
    cD
    cT
    cE
    cH
    cK
    chlt
    cW
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @2
    eqid
    erngbase
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
    @4
    vb
    cv
    cfv
    ccom
    cmpt
    cmpt2
    cP
    vb
    cD
    @3
    cT
    vf
    cE
    cH
    cK
    chlt
    cW
    va
    ernggrp.h
    erngdv.t
    erngdv.e
    ernggrp.d
    @3
    eqid
    erngfplus
    erngdv.p
    syl6reqr
    vb
    cP
    cT
    @1
    vf
    cE
    cH
    cK
    vt
    cv
    #
    cW
    va
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.p
    tendoplcl
    vb
    cP
    @1
    cT
    @5
    vf
    cE
    cH
    cK
    vu
    cv
    cW
    va
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.p
    tendoplass
    cB
    cT
    vf
    cE
    cH
    cK
    c.0
    cW
    erngdv.b
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.o
    tendo0cl
    vb
    cB
    cP
    @1
    cT
    vf
    cE
    cH
    cK
    c.0
    cW
    va
    erngdv.b
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.o
    erngdv.p
    tendo0pl
    @1
    cT
    vf
    cE
    cH
    cI
    cK
    cW
    va
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.i
    tendoicl
    vb
    cB
    cP
    @1
    cT
    vf
    cE
    cH
    cI
    cK
    c.0
    cW
    va
    ernggrp.h
    erngdv.t
    erngdv.e
    erngdv.i
    erngdv.b
    erngdv.p
    erngdv.o
    tendoipl
    isgrpd
end
