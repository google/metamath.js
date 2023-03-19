include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2l.mm"
include "simp2r.mm"
include "co.mm"
include "cc0.mm"
include "cr.mm"
include "wceq.mm"
include "xmet0.mm"
include "3ad2ant1.mm"
include "0re.mm"
include "syl6eqel.mm"
include "cxne.mm"
include "cxad.mm"
include "simp3.mm"
include "wb.mm"
include "xsubge0.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "xblss2.mm"

theorem ssbl
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cX: class X
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  let cC: class C


  assert |- ( ( ( D e. ( *Met ` X ) /\ P e. X ) /\ ( R e. RR* /\ S e. RR* ) /\ R <_ S ) -> ( P ( ball ` D ) R ) C_ ( P ( ball ` D ) S ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    wa
    #
    cR
    cxr
    wcel
    #
    cS
    cxr
    wcel
    #
    wa
    #
    cR
    cS
    cle
    wbr
    #
    w3a
    #
    cD
    cP
    cP
    cR
    cS
    cX
    @0
    @1
    @5
    @6
    simp1l
    @0
    @1
    @5
    @6
    simp1r
    #
    @8
    @2
    @3
    @4
    @6
    simp2l
    #
    @2
    @3
    @4
    @6
    simp2r
    #
    @7
    cP
    cP
    cD
    co
    #
    cc0
    cr
    @2
    @5
    @11
    cc0
    wceq
    @6
    cP
    cD
    cX
    xmet0
    3ad2ant1
    #
    0re
    syl6eqel
    @7
    @11
    cc0
    cS
    cR
    cxne
    cxad
    co
    #
    cle
    @12
    @7
    cc0
    @13
    cle
    wbr
    #
    @6
    @2
    @5
    @6
    simp3
    @7
    @4
    @3
    @14
    @6
    wb
    @10
    @9
    cS
    cR
    xsubge0
    syl2anc
    mpbird
    eqbrtrd
    xblss2
end
