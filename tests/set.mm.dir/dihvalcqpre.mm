include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "cvv.mm"
include "cfv.mm"
include "clss.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cv.mm"
include "nfv.mm"
include "nfvd.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "dihvalc.mm"
include "3adant3.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantl.mm"
include "simpl1.mm"
include "simprl.mm"
include "simprrl.mm"
include "jca.mm"
include "simpl3l.mm"
include "simpl2l.mm"
include "simprrr.mm"
include "simpl3r.mm"
include "eqtr4d.mm"
include "dihjust.mm"
include "syl131anc.mm"
include "ex.mm"
include "dihlsscpre.mm"
include "wrex.mm"
include "lhpmcvr2.mm"
include "riotasv3d.mm"
include "mpan2.mm"

theorem dihvalcqpre
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.po: class .(+)
  let cQ: class Q
  let cS: class S
  let cU: class U
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let vk: setvar k
  let vq: setvar q
  let vw: setvar w
  let vu: setvar u
  let vx: setvar x
  let vr: setvar r
  assume dihval.b: |- B = ( Base ` K )
  assume dihval.l: |- .<_ = ( le ` K )
  assume dihval.j: |- .\/ = ( join ` K )
  assume dihval.m: |- ./\ = ( meet ` K )
  assume dihval.a: |- A = ( Atoms ` K )
  assume dihval.h: |- H = ( LHyp ` K )
  assume dihval.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dihval.d: |- D = ( ( DIsoB ` K ) ` W )
  assume dihval.c: |- C = ( ( DIsoC ` K ) ` W )
  assume dihval.u: |- U = ( ( DVecH ` K ) ` W )
  assume dihval.s: |- S = ( LSubSp ` U )
  assume dihval.p: |- .(+) = ( LSSum ` U )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) /\ ( ( Q e. A /\ -. Q .<_ W ) /\ ( Q .\/ ( X ./\ W ) ) = X ) ) -> ( I ` X ) = ( ( C ` Q ) .(+) ( D ` ( X ./\ W ) ) ) )

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
    cB
    wcel
    #
    cX
    cW
    c.le
    wbr
    wn
    #
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
    cQ
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    w3a
    #
    cS
    cvv
    wcel
    cX
    cI
    cfv
    #
    cQ
    cC
    cfv
    @5
    cD
    cfv
    #
    c.po
    co
    #
    wceq
    #
    cS
    cU
    clss
    cfv
    cvv
    dihval.s
    cU
    clss
    fvex
    eqeltri
    @9
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @14
    @5
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    @14
    cC
    cfv
    @11
    c.po
    co
    #
    @12
    wceq
    #
    @13
    vu
    vq
    cS
    cA
    @19
    @10
    cvv
    @9
    vq
    nfv
    @9
    @13
    vq
    nfvd
    @0
    @3
    @10
    @18
    vu
    cv
    @19
    wceq
    wi
    vq
    cA
    wral
    vu
    cS
    crio
    wceq
    @8
    vu
    cA
    cB
    cC
    cD
    c.po
    cS
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    chlt
    cW
    cX
    vq
    dihval.b
    dihval.l
    dihval.j
    dihval.m
    dihval.a
    dihval.h
    dihval.i
    dihval.d
    dihval.c
    dihval.u
    dihval.s
    dihval.p
    dihvalc
    3adant3
    @19
    @10
    wceq
    @20
    @13
    wb
    @9
    @19
    @10
    @12
    eqeq1
    adantl
    @9
    @14
    cA
    wcel
    #
    @18
    wa
    #
    @20
    @9
    @22
    wa
    #
    @0
    @21
    @15
    wa
    @4
    @1
    @16
    @6
    wceq
    @20
    @0
    @3
    @8
    @22
    simpl1
    @23
    @21
    @15
    @9
    @21
    @18
    simprl
    @9
    @21
    @15
    @17
    simprrl
    jca
    @4
    @7
    @0
    @3
    @22
    simpl3l
    @1
    @2
    @0
    @8
    @22
    simpl2l
    @23
    @16
    cX
    @6
    @9
    @21
    @15
    @17
    simprrr
    @4
    @7
    @0
    @3
    @22
    simpl3r
    eqtr4d
    cA
    cB
    c.po
    @14
    cQ
    cU
    cH
    cD
    cC
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihval.b
    dihval.l
    dihval.j
    dihval.m
    dihval.a
    dihval.h
    dihval.d
    dihval.c
    dihval.u
    dihval.p
    dihjust
    syl131anc
    ex
    @0
    @3
    @10
    cS
    wcel
    @8
    cA
    cB
    cC
    cD
    c.po
    cS
    cU
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cW
    cX
    dihval.b
    dihval.l
    dihval.j
    dihval.m
    dihval.a
    dihval.h
    dihval.i
    dihval.d
    dihval.c
    dihval.u
    dihval.s
    dihval.p
    dihlsscpre
    3adant3
    @0
    @3
    @18
    vq
    cA
    wrex
    @8
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cX
    vq
    dihval.b
    dihval.l
    dihval.j
    dihval.m
    dihval.a
    dihval.h
    lhpmcvr2
    3adant3
    riotasv3d
    mpan2
end
