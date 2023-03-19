include "cmbf.mm"
include "wcel.mm"
include "cr.mm"
include "wf.mm"
include "wa.mm"
include "cxr.mm"
include "ccnv.mm"
include "cioo.mm"
include "co.mm"
include "cima.mm"
include "cvol.mm"
include "cdm.mm"
include "cv.mm"
include "crn.mm"
include "wral.mm"
include "ismbf.mm"
include "biimpac.mm"
include "cxp.mm"
include "wfn.mm"
include "cpw.mm"
include "ioof.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fnovrn.mm"
include "mp3an1.mm"
include "wceq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "wn.mm"
include "c0.mm"
include "ndmioo.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "syl6eq.mm"
include "0mbl.mm"
include "syl6eqel.mm"
include "adantl.mm"
include "pm2.61dan.mm"

theorem mbfima
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. MblFn /\ F : A --> RR ) -> ( `' F " ( B (,) C ) ) e. dom vol )

  proof
    cF
    cmbf
    wcel
    #
    cA
    cr
    cF
    wf
    #
    wa
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    wa
    #
    cF
    ccnv
    #
    cB
    cC
    cioo
    co
    #
    cima
    #
    cvol
    cdm
    #
    wcel
    #
    @2
    @6
    vx
    cv
    #
    cima
    #
    @9
    wcel
    #
    vx
    cioo
    crn
    #
    wral
    #
    @7
    @14
    wcel
    #
    @10
    @5
    @1
    @0
    @15
    vx
    cA
    cF
    ismbf
    biimpac
    cioo
    cxr
    cxr
    cxp
    #
    wfn
    #
    @3
    @4
    @16
    @17
    cr
    cpw
    #
    cioo
    wf
    @18
    ioof
    @17
    @19
    cioo
    ffn
    ax-mp
    cxr
    cxr
    cB
    cC
    cioo
    fnovrn
    mp3an1
    @13
    @10
    vx
    @7
    @14
    @11
    @7
    wceq
    @12
    @8
    @9
    @11
    @7
    @6
    imaeq2
    eleq1d
    rspccva
    syl2an
    @5
    wn
    #
    @10
    @2
    @20
    @8
    c0
    @9
    @20
    @8
    @6
    c0
    cima
    c0
    @20
    @7
    c0
    @6
    cB
    cC
    ndmioo
    imaeq2d
    @6
    ima0
    syl6eq
    0mbl
    syl6eqel
    adantl
    pm2.61dan
end
