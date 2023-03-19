include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "w3a.mm"
include "cfv.mm"
include "cop.mm"
include "co.mm"
include "ccom.mm"
include "csca.mm"
include "cplusg.mm"
include "wceq.mm"
include "simp1.mm"
include "simp3l.mm"
include "lhpocnel2.mm"
include "syl.mm"
include "simp2l.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "tendocl.mm"
include "simp3r.mm"
include "tendo0cl.mm"
include "eqid.mm"
include "dvhopvadd.mm"
include "syl122anc.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "dvhfplusr.mm"
include "oveqd.mm"
include "tendo0plr.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "opeq2d.mm"

theorem cdlemn6
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cW: class W
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  assume cdlemn8.b: |- B = ( Base ` K )
  assume cdlemn8.l: |- .<_ = ( le ` K )
  assume cdlemn8.a: |- A = ( Atoms ` K )
  assume cdlemn8.h: |- H = ( LHyp ` K )
  assume cdlemn8.p: |- P = ( ( oc ` K ) ` W )
  assume cdlemn8.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume cdlemn8.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn8.e: |- E = ( ( TEndo ` K ) ` W )
  assume cdlemn8.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn8.s: |- .+ = ( +g ` U )
  assume cdlemn8.f: |- F = ( iota_ h e. T ( h ` P ) = Q )

  disjoint .<_ h
  disjoint A h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint T h
  disjoint P h
  disjoint Q h
  disjoint W h
  disjoint h t
  disjoint h u
  disjoint t u
  disjoint K t
  disjoint K u
  disjoint T t
  disjoint T u
  disjoint E t
  disjoint E u
  disjoint W t
  disjoint W u
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) /\ ( s e. E /\ g e. T ) ) -> ( <. ( s ` F ) , s >. .+ <. g , O >. ) = <. ( ( s ` F ) o. g ) , s >. )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    vs
    cv
    #
    cE
    wcel
    #
    vg
    cv
    #
    cT
    wcel
    #
    wa
    #
    w3a
    #
    cF
    @4
    cfv
    #
    @4
    cop
    @6
    cO
    cop
    c.pl
    co
    #
    @10
    @6
    ccom
    #
    @4
    cO
    cU
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cop
    #
    @12
    @4
    cop
    @9
    @0
    @10
    cT
    wcel
    #
    @5
    @7
    cO
    cE
    wcel
    #
    @11
    @16
    wceq
    @0
    @3
    @8
    simp1
    #
    @9
    @0
    @5
    cF
    cT
    wcel
    #
    @17
    @19
    @0
    @3
    @5
    @7
    simp3l
    #
    @9
    @0
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    @1
    @20
    @19
    @9
    @0
    @22
    @19
    cA
    cP
    cH
    cK
    c.le
    cW
    cdlemn8.l
    cdlemn8.a
    cdlemn8.h
    cdlemn8.p
    lhpocnel2
    syl
    @0
    @1
    @2
    @8
    simp2l
    cA
    cP
    cQ
    cT
    vh
    cF
    cH
    cK
    c.le
    cW
    cdlemn8.l
    cdlemn8.a
    cdlemn8.h
    cdlemn8.t
    cdlemn8.f
    ltrniotacl
    syl3anc
    @4
    cT
    cE
    cF
    cH
    cK
    chlt
    cW
    cdlemn8.h
    cdlemn8.t
    cdlemn8.e
    tendocl
    syl3anc
    @21
    @0
    @3
    @5
    @7
    simp3r
    @9
    @0
    @18
    @19
    cB
    cT
    vh
    cE
    cH
    cK
    cO
    cW
    cdlemn8.b
    cdlemn8.h
    cdlemn8.t
    cdlemn8.e
    cdlemn8.o
    tendo0cl
    syl
    @13
    c.pl
    @14
    @4
    cO
    cT
    cU
    cE
    @10
    @6
    cH
    cK
    cW
    cdlemn8.h
    cdlemn8.t
    cdlemn8.e
    cdlemn8.u
    @13
    eqid
    #
    cdlemn8.s
    @14
    eqid
    #
    dvhopvadd
    syl122anc
    @9
    @15
    @4
    @12
    @9
    @15
    @4
    cO
    vt
    vu
    cE
    cE
    vh
    cT
    vh
    cv
    #
    vt
    cv
    cfv
    @25
    vu
    cv
    cfv
    ccom
    cmpt
    cmpt2
    #
    co
    #
    @4
    @9
    @14
    @26
    @4
    cO
    @9
    @0
    @14
    @26
    wceq
    @19
    vu
    @26
    @14
    cT
    cU
    vh
    cE
    @13
    cH
    cK
    chlt
    cW
    vt
    cdlemn8.h
    cdlemn8.t
    cdlemn8.e
    cdlemn8.u
    @23
    @26
    eqid
    #
    @24
    dvhfplusr
    syl
    oveqd
    @9
    @0
    @5
    @27
    @4
    wceq
    @19
    @21
    vu
    cB
    @26
    @4
    cT
    vh
    cE
    cH
    cK
    cO
    cW
    vt
    cdlemn8.b
    cdlemn8.h
    cdlemn8.t
    cdlemn8.e
    cdlemn8.o
    @28
    tendo0plr
    syl2anc
    eqtrd
    opeq2d
    eqtrd
end
