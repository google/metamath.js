include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "marrepval.mm"
include "3adant3.mm"
include "cvv.mm"
include "simp3l.mm"
include "simpl3r.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ifexg.mm"
include "mpan2.mm"
include "ovexd.mm"
include "ifcld.mm"
include "adantl.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "wb.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "oveq12.mm"
include "ifbieq12d.mm"
include "ovmpt2dv2.mm"
include "mpd.mm"

theorem marrepeval
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let c.0: class .0.
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume marrepfval.a: |- A = ( N Mat R )
  assume marrepfval.b: |- B = ( Base ` A )
  assume marrepfval.q: |- Q = ( N matRRep R )
  assume marrepfval.z: |- .0. = ( 0g ` R )


  assert |- ( ( ( M e. B /\ S e. ( Base ` R ) ) /\ ( K e. N /\ L e. N ) /\ ( I e. N /\ J e. N ) ) -> ( I ( K ( M Q S ) L ) J ) = if ( I = K , if ( J = L , S , .0. ) , ( I M J ) ) )

  proof
    cM
    cB
    wcel
    #
    cS
    cR
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    cK
    cN
    wcel
    cL
    cN
    wcel
    wa
    #
    cI
    cN
    wcel
    #
    cJ
    cN
    wcel
    #
    wa
    #
    w3a
    #
    cK
    cL
    cM
    cS
    cQ
    co
    co
    #
    vi
    vj
    cN
    cN
    vi
    cv
    #
    cK
    wceq
    #
    vj
    cv
    #
    cL
    wceq
    #
    cS
    c.0
    cif
    #
    @10
    @12
    cM
    co
    #
    cif
    #
    cmpt2
    wceq
    #
    cI
    cJ
    @9
    co
    cI
    cK
    wceq
    #
    cJ
    cL
    wceq
    #
    cS
    c.0
    cif
    #
    cI
    cJ
    cM
    co
    #
    cif
    #
    wceq
    @3
    @4
    @17
    @7
    cA
    cB
    cQ
    cR
    cS
    vi
    vj
    cK
    cL
    cM
    cN
    c.0
    marrepfval.a
    marrepfval.b
    marrepfval.q
    marrepfval.z
    marrepval
    3adant3
    @8
    vi
    vj
    cI
    cJ
    cN
    cN
    @16
    @22
    @9
    cvv
    @3
    @4
    @5
    @6
    simp3l
    @5
    @6
    @3
    @4
    @10
    cI
    wceq
    #
    simpl3r
    @8
    @16
    cvv
    wcel
    #
    @23
    @12
    cJ
    wceq
    #
    wa
    #
    @3
    @4
    @24
    @7
    @2
    @24
    @0
    @2
    @11
    @14
    @15
    cvv
    @2
    c.0
    cvv
    wcel
    @14
    cvv
    wcel
    c.0
    cR
    c0g
    cfv
    cvv
    marrepfval.z
    cR
    c0g
    fvex
    eqeltri
    @13
    cS
    c.0
    @1
    cvv
    ifexg
    mpan2
    @2
    @10
    @12
    cM
    ovexd
    ifcld
    adantl
    3ad2ant1
    adantr
    @26
    @16
    @22
    wceq
    @8
    @26
    @11
    @18
    @14
    @15
    @20
    @21
    @23
    @11
    @18
    wb
    @25
    @10
    cI
    cK
    eqeq1
    adantr
    @25
    @14
    @20
    wceq
    @23
    @25
    @13
    @19
    cS
    c.0
    @12
    cJ
    cL
    eqeq1
    ifbid
    adantl
    @10
    cI
    @12
    cJ
    cM
    oveq12
    ifbieq12d
    adantl
    ovmpt2dv2
    mpd
end
