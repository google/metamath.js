include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "marepvval.mm"
include "adantr.mm"
include "cvv.mm"
include "simprl.mm"
include "simplrr.mm"
include "fvexd.mm"
include "ovexd.mm"
include "ifcld.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantl.mm"
include "fveq2.mm"
include "oveq12.mm"
include "ifbieq12d.mm"
include "ovmpt2dv2.mm"
include "mpd.mm"

theorem marepveval
  let cA: class A
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let cN: class N
  let cV: class V
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vv: setvar v
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vc: setvar c
  assume marepvfval.a: |- A = ( N Mat R )
  assume marepvfval.b: |- B = ( Base ` A )
  assume marepvfval.q: |- Q = ( N matRepV R )
  assume marepvfval.v: |- V = ( ( Base ` R ) ^m N )


  assert |- ( ( ( M e. B /\ C e. V /\ K e. N ) /\ ( I e. N /\ J e. N ) ) -> ( I ( ( M Q C ) ` K ) J ) = if ( J = K , ( C ` I ) , ( I M J ) ) )

  proof
    cM
    cB
    wcel
    cC
    cV
    wcel
    cK
    cN
    wcel
    w3a
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
    wa
    #
    cK
    cM
    cC
    cQ
    co
    cfv
    #
    vi
    vj
    cN
    cN
    vj
    cv
    #
    cK
    wceq
    #
    vi
    cv
    #
    cC
    cfv
    #
    @8
    @6
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
    @5
    co
    cJ
    cK
    wceq
    #
    cI
    cC
    cfv
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
    @12
    @3
    cA
    cB
    cC
    cQ
    cR
    vi
    vj
    cK
    cM
    cN
    cV
    marepvfval.a
    marepvfval.b
    marepvfval.q
    marepvfval.v
    marepvval
    adantr
    @4
    vi
    vj
    cI
    cJ
    cN
    cN
    @11
    @16
    @5
    cvv
    @0
    @1
    @2
    simprl
    @0
    @1
    @2
    @8
    cI
    wceq
    #
    simplrr
    @4
    @11
    cvv
    wcel
    @17
    @6
    cJ
    wceq
    #
    wa
    #
    @4
    @7
    @9
    @10
    cvv
    @4
    @8
    cC
    fvexd
    @4
    @8
    @6
    cM
    ovexd
    ifcld
    adantr
    @19
    @11
    @16
    wceq
    @4
    @19
    @7
    @13
    @9
    @10
    @14
    @15
    @18
    @7
    @13
    wb
    @17
    @6
    cJ
    cK
    eqeq1
    adantl
    @17
    @9
    @14
    wceq
    @18
    @8
    cI
    cC
    fveq2
    adantr
    @8
    cI
    @6
    cJ
    cM
    oveq12
    ifbieq12d
    adantl
    ovmpt2dv2
    mpd
end
