include "cr.mm"
include "wf.mm"
include "c0p.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "wa.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "wral.mm"
include "ffn.mm"
include "adantr.mm"
include "csn.mm"
include "cxp.mm"
include "cc.mm"
include "wss.mm"
include "ax-resscn.mm"
include "a1i.mm"
include "0pledm.mm"
include "cvv.mm"
include "0re.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "reex.mm"
include "inidm.mm"
include "wceq.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "eqidd.mm"
include "ofrfval.mm"
include "cxr.mm"
include "ffvelrn.mm"
include "rexrd.mm"
include "biantrurd.mm"
include "elxrge0.mm"
include "syl6bbr.mm"
include "ralbidva.mm"
include "3bitrd.mm"
include "biimpa.mm"
include "ffnfv.mm"
include "sylanbrc.mm"

theorem xrge0f
  let cF: class F
  let vg: setvar g
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vh: setvar h
  let vy: setvar y
  let cG: class G


  assert |- ( ( F : RR --> RR /\ 0p oR <_ F ) -> F : RR --> ( 0 [,] +oo ) )

  proof
    cr
    cr
    cF
    wf
    #
    c0p
    cF
    cle
    cofr
    #
    wbr
    #
    wa
    cF
    cr
    wfn
    #
    vx
    cv
    #
    cF
    cfv
    #
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    vx
    cr
    wral
    #
    cr
    @6
    cF
    wf
    @0
    @3
    @2
    cr
    cr
    cF
    ffn
    #
    adantr
    @0
    @2
    @8
    @0
    @2
    cr
    cc0
    csn
    cxp
    #
    cF
    @1
    wbr
    cc0
    @5
    cle
    wbr
    #
    vx
    cr
    wral
    @8
    @0
    cr
    cF
    cr
    cc
    wss
    @0
    ax-resscn
    a1i
    @9
    0pledm
    @0
    vx
    cr
    cr
    cc0
    @5
    cle
    cr
    @10
    cF
    cvv
    cvv
    cc0
    cr
    wcel
    @10
    cr
    wfn
    @0
    0re
    cr
    cc0
    cr
    fnconstg
    mp1i
    @9
    cr
    cvv
    wcel
    @0
    reex
    a1i
    #
    @12
    cr
    inidm
    @4
    cr
    wcel
    #
    @4
    @10
    cfv
    cc0
    wceq
    @0
    cr
    cc0
    @4
    c0ex
    fvconst2
    adantl
    @0
    @13
    wa
    #
    @5
    eqidd
    ofrfval
    @0
    @11
    @7
    vx
    cr
    @14
    @11
    @5
    cxr
    wcel
    #
    @11
    wa
    @7
    @14
    @15
    @11
    @14
    @5
    cr
    cr
    @4
    cF
    ffvelrn
    rexrd
    biantrurd
    @5
    elxrge0
    syl6bbr
    ralbidva
    3bitrd
    biimpa
    vx
    cr
    @6
    cF
    ffnfv
    sylanbrc
end
