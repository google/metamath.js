include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "submaval.mm"
include "3expb.mm"
include "3adant3.mm"
include "cvv.mm"
include "simp3l.mm"
include "simpl3r.mm"
include "ovexd.mm"
include "oveq12.mm"
include "adantl.mm"
include "ovmpt2dv2.mm"
include "mpd.mm"

theorem submaeval
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume submafval.a: |- A = ( N Mat R )
  assume submafval.q: |- Q = ( N subMat R )
  assume submafval.b: |- B = ( Base ` A )


  assert |- ( ( M e. B /\ ( K e. N /\ L e. N ) /\ ( I e. ( N \ { K } ) /\ J e. ( N \ { L } ) ) ) -> ( I ( K ( Q ` M ) L ) J ) = ( I M J ) )

  proof
    cM
    cB
    wcel
    #
    cK
    cN
    wcel
    #
    cL
    cN
    wcel
    #
    wa
    #
    cI
    cN
    cK
    csn
    cdif
    #
    wcel
    #
    cJ
    cN
    cL
    csn
    cdif
    #
    wcel
    #
    wa
    #
    w3a
    #
    cK
    cL
    cM
    cQ
    cfv
    co
    #
    vi
    vj
    @4
    @6
    vi
    cv
    #
    vj
    cv
    #
    cM
    co
    #
    cmpt2
    wceq
    #
    cI
    cJ
    @10
    co
    cI
    cJ
    cM
    co
    #
    wceq
    @0
    @3
    @14
    @8
    @0
    @1
    @2
    @14
    cA
    cB
    cQ
    cR
    vi
    vj
    cK
    cL
    cM
    cN
    submafval.a
    submafval.q
    submafval.b
    submaval
    3expb
    3adant3
    @9
    vi
    vj
    cI
    cJ
    @4
    @6
    @13
    @15
    @10
    cvv
    @0
    @3
    @5
    @7
    simp3l
    @5
    @7
    @0
    @3
    @11
    cI
    wceq
    #
    simpl3r
    @9
    @16
    @12
    cJ
    wceq
    wa
    #
    wa
    @11
    @12
    cM
    ovexd
    @17
    @13
    @15
    wceq
    @9
    @11
    cI
    @12
    cJ
    cM
    oveq12
    adantl
    ovmpt2dv2
    mpd
end
