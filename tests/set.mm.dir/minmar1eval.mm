include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "minmar1val.mm"
include "3expb.mm"
include "3adant3.mm"
include "cvv.mm"
include "simp3l.mm"
include "simpl3r.mm"
include "cur.mm"
include "fvex.mm"
include "eqeltri.mm"
include "c0g.mm"
include "ifex.mm"
include "ovex.mm"
include "a1i.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantr.mm"
include "adantl.mm"
include "ifbid.mm"
include "oveq12.mm"
include "ifbieq12d.mm"
include "ovmpt2dv2.mm"
include "mpd.mm"

theorem minmar1eval
  let cA: class A
  let cB: class B
  let cQ: class Q
  let cR: class R
  let c.1: class .1.
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
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vl: setvar l
  assume minmar1fval.a: |- A = ( N Mat R )
  assume minmar1fval.b: |- B = ( Base ` A )
  assume minmar1fval.q: |- Q = ( N minMatR1 R )
  assume minmar1fval.o: |- .1. = ( 1r ` R )
  assume minmar1fval.z: |- .0. = ( 0g ` R )


  assert |- ( ( M e. B /\ ( K e. N /\ L e. N ) /\ ( I e. N /\ J e. N ) ) -> ( I ( K ( Q ` M ) L ) J ) = if ( I = K , if ( J = L , .1. , .0. ) , ( I M J ) ) )

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
    cQ
    cfv
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
    c.1
    c.0
    cif
    #
    @9
    @11
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
    @8
    co
    cI
    cK
    wceq
    #
    cJ
    cL
    wceq
    #
    c.1
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
    @0
    @3
    @16
    @6
    @0
    @1
    @2
    @16
    cA
    cB
    cQ
    cR
    c.1
    vi
    vj
    cK
    cL
    cM
    cN
    c.0
    minmar1fval.a
    minmar1fval.b
    minmar1fval.q
    minmar1fval.o
    minmar1fval.z
    minmar1val
    3expb
    3adant3
    @7
    vi
    vj
    cI
    cJ
    cN
    cN
    @15
    @21
    @8
    cvv
    @0
    @3
    @4
    @5
    simp3l
    @4
    @5
    @0
    @3
    @9
    cI
    wceq
    #
    simpl3r
    @15
    cvv
    wcel
    @7
    @22
    @11
    cJ
    wceq
    #
    wa
    #
    wa
    @10
    @13
    @14
    @12
    c.1
    c.0
    c.1
    cR
    cur
    cfv
    cvv
    minmar1fval.o
    cR
    cur
    fvex
    eqeltri
    c.0
    cR
    c0g
    cfv
    cvv
    minmar1fval.z
    cR
    c0g
    fvex
    eqeltri
    ifex
    @9
    @11
    cM
    ovex
    ifex
    a1i
    @24
    @15
    @21
    wceq
    @7
    @24
    @10
    @17
    @13
    @14
    @19
    @20
    @22
    @10
    @17
    wb
    @23
    @9
    cI
    cK
    eqeq1
    adantr
    @24
    @12
    @18
    c.1
    c.0
    @23
    @12
    @18
    wb
    @22
    @11
    cJ
    cL
    eqeq1
    adantl
    ifbid
    @9
    cI
    @11
    cJ
    cM
    oveq12
    ifbieq12d
    adantl
    ovmpt2dv2
    mpd
end
