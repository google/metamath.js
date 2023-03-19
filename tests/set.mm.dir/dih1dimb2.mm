include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cv.mm"
include "ctrl.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cop.mm"
include "csn.mm"
include "eqid.mm"
include "cdlemf.mm"
include "w3a.mm"
include "simp3.mm"
include "simp1rl.mm"
include "eqeltrd.mm"
include "wb.mm"
include "simp1l.mm"
include "simp2.mm"
include "trlnidatb.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "fveq2d.mm"
include "dih1dimb.mm"
include "eqtr3d.mm"
include "jca.mm"
include "3expia.mm"
include "reximdva.mm"
include "mpd.mm"

theorem dih1dimb2
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vh: setvar h
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cN: class N
  let cO: class O
  let cW: class W
  assume dih1dimb2.b: |- B = ( Base ` K )
  assume dih1dimb2.l: |- .<_ = ( le ` K )
  assume dih1dimb2.a: |- A = ( Atoms ` K )
  assume dih1dimb2.h: |- H = ( LHyp ` K )
  assume dih1dimb2.t: |- T = ( ( LTrn ` K ) ` W )
  assume dih1dimb2.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume dih1dimb2.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih1dimb2.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih1dimb2.n: |- N = ( LSpan ` U )

  disjoint .<_ f
  disjoint A f
  disjoint B h
  disjoint H f
  disjoint f h
  disjoint K f
  disjoint K h
  disjoint Q f
  disjoint T f
  disjoint T h
  disjoint W f
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ Q .<_ W ) ) -> E. f e. T ( f =/= ( _I |` B ) /\ ( I ` Q ) = ( N ` { <. f , O >. } ) ) )

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
    #
    cQ
    cW
    c.le
    wbr
    #
    wa
    #
    wa
    #
    vf
    cv
    #
    cW
    cK
    ctrl
    cfv
    cfv
    #
    cfv
    #
    cQ
    wceq
    #
    vf
    cT
    wrex
    @5
    cid
    cB
    cres
    wne
    #
    cQ
    cI
    cfv
    #
    @5
    cO
    cop
    csn
    cN
    cfv
    #
    wceq
    #
    wa
    #
    vf
    cT
    wrex
    cA
    @6
    cT
    cQ
    vf
    cH
    cK
    c.le
    cW
    dih1dimb2.l
    dih1dimb2.a
    dih1dimb2.h
    dih1dimb2.t
    @6
    eqid
    #
    cdlemf
    @4
    @8
    @13
    vf
    cT
    @4
    @5
    cT
    wcel
    #
    @8
    @13
    @4
    @15
    @8
    w3a
    #
    @9
    @12
    @16
    @9
    @7
    cA
    wcel
    #
    @16
    @7
    cQ
    cA
    @4
    @15
    @8
    simp3
    #
    @1
    @2
    @0
    @15
    @8
    simp1rl
    eqeltrd
    @16
    @0
    @15
    @9
    @17
    wb
    @0
    @3
    @15
    @8
    simp1l
    #
    @4
    @15
    @8
    simp2
    #
    cA
    cB
    @6
    cT
    @5
    cH
    cK
    cW
    dih1dimb2.b
    dih1dimb2.a
    dih1dimb2.h
    dih1dimb2.t
    @14
    trlnidatb
    syl2anc
    mpbird
    @16
    @7
    cI
    cfv
    #
    @10
    @11
    @16
    @7
    cQ
    cI
    @18
    fveq2d
    @16
    @0
    @15
    @21
    @11
    wceq
    @19
    @20
    cB
    @6
    cT
    cU
    vh
    @5
    cH
    cI
    cK
    cN
    cO
    cW
    dih1dimb2.b
    dih1dimb2.h
    dih1dimb2.t
    @14
    dih1dimb2.o
    dih1dimb2.u
    dih1dimb2.i
    dih1dimb2.n
    dih1dimb
    syl2anc
    eqtr3d
    jca
    3expia
    reximdva
    mpd
end
