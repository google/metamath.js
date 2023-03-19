include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "c2.mm"
include "cxmu.mm"
include "cxad.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "psmettri2.mm"
include "syl13anc.mm"
include "wceq.mm"
include "psmet0.mm"
include "3adant2.mm"
include "cr.mm"
include "cxr.mm"
include "2re.mm"
include "rexr.mm"
include "xmul01.mm"
include "mp2b.mm"
include "syl6reqr.mm"
include "psmetcl.mm"
include "x2times.mm"
include "syl.mm"
include "3brtr4d.mm"
include "crp.mm"
include "wb.mm"
include "0xr.mm"
include "a1i.mm"
include "2rp.mm"
include "xlemul2.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem psmetge0
  let cA: class A
  let cB: class B
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cC: class C


  assert |- ( ( D e. ( PsMet ` X ) /\ A e. X /\ B e. X ) -> 0 <_ ( A D B ) )

  proof
    cD
    cX
    cpsmet
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cc0
    cA
    cB
    cD
    co
    #
    cle
    wbr
    #
    c2
    cc0
    cxmu
    co
    #
    c2
    @4
    cxmu
    co
    #
    cle
    wbr
    #
    @3
    cB
    cB
    cD
    co
    #
    @4
    @4
    cxad
    co
    #
    @6
    @7
    cle
    @3
    @0
    @1
    @2
    @2
    @9
    @10
    cle
    wbr
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    #
    @11
    cB
    cB
    cA
    cD
    cX
    psmettri2
    syl13anc
    @3
    @9
    cc0
    @6
    @0
    @2
    @9
    cc0
    wceq
    @1
    cB
    cD
    cX
    psmet0
    3adant2
    c2
    cr
    wcel
    c2
    cxr
    wcel
    @6
    cc0
    wceq
    2re
    c2
    rexr
    c2
    xmul01
    mp2b
    syl6reqr
    @3
    @4
    cxr
    wcel
    #
    @7
    @10
    wceq
    cA
    cB
    cD
    cX
    psmetcl
    #
    @4
    x2times
    syl
    3brtr4d
    @3
    cc0
    cxr
    wcel
    #
    @12
    c2
    crp
    wcel
    #
    @5
    @8
    wb
    @14
    @3
    0xr
    a1i
    @13
    @15
    @3
    2rp
    a1i
    cc0
    @4
    c2
    xlemul2
    syl3anc
    mpbird
end
