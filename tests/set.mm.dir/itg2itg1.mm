include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "c0p.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "wa.mm"
include "citg2.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "itg1le.mm"
include "3expia.mm"
include "ancoms.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cxr.mm"
include "wb.mm"
include "i1ff.mm"
include "xrge0f.mm"
include "sylan.mm"
include "itg1cl.mm"
include "rexrd.mm"
include "itg2leub.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "simpl.mm"
include "cvv.mm"
include "reex.mm"
include "a1i.mm"
include "leid.mm"
include "adantl.mm"
include "caofref.mm"
include "itg2ub.mm"
include "syl3anc.mm"
include "itg2cl.mm"
include "syl.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem itg2itg1
  let cF: class F
  let vg: setvar g
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vh: setvar h
  let vy: setvar y
  let cG: class G


  assert |- ( ( F e. dom S.1 /\ 0p oR <_ F ) -> ( S.2 ` F ) = ( S.1 ` F ) )

  proof
    cF
    citg1
    cdm
    #
    wcel
    #
    c0p
    cF
    cle
    cofr
    #
    wbr
    #
    wa
    #
    cF
    citg2
    cfv
    #
    cF
    citg1
    cfv
    #
    wceq
    #
    @5
    @6
    cle
    wbr
    #
    @6
    @5
    cle
    wbr
    #
    @4
    @8
    vg
    cv
    #
    cF
    @2
    wbr
    #
    @10
    citg1
    cfv
    @6
    cle
    wbr
    #
    wi
    #
    vg
    @0
    wral
    #
    @1
    @14
    @3
    @1
    @13
    vg
    @0
    @10
    @0
    wcel
    #
    @1
    @13
    @15
    @1
    @11
    @12
    @10
    cF
    itg1le
    3expia
    ancoms
    ralrimiva
    adantr
    @4
    cr
    cc0
    cpnf
    cicc
    co
    cF
    wf
    #
    @6
    cxr
    wcel
    #
    @8
    @14
    wb
    @1
    cr
    cr
    cF
    wf
    @3
    @16
    cF
    i1ff
    #
    cF
    xrge0f
    sylan
    #
    @4
    @6
    @1
    @6
    cr
    wcel
    @3
    cF
    itg1cl
    adantr
    rexrd
    #
    @6
    vg
    cF
    itg2leub
    syl2anc
    mpbird
    @4
    @16
    @1
    cF
    cF
    @2
    wbr
    #
    @9
    @19
    @1
    @3
    simpl
    @1
    @21
    @3
    @1
    vx
    cr
    cle
    cr
    cF
    cvv
    cr
    cvv
    wcel
    @1
    reex
    a1i
    @18
    vx
    cv
    #
    cr
    wcel
    @22
    @22
    cle
    wbr
    @1
    @22
    leid
    adantl
    caofref
    adantr
    cF
    cF
    itg2ub
    syl3anc
    @4
    @5
    cxr
    wcel
    #
    @17
    @7
    @8
    @9
    wa
    wb
    @4
    @16
    @23
    @19
    cF
    itg2cl
    syl
    @20
    @5
    @6
    xrletri3
    syl2anc
    mpbir2and
end
