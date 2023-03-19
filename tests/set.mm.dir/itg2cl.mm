include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "citg2.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "citg1.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "eqid.mm"
include "itg2val.mm"
include "wss.mm"
include "wcel.mm"
include "itg2lcl.mm"
include "supxrcl.mm"
include "ax-mp.mm"
include "syl6eqel.mm"

theorem itg2cl
  let cF: class F
  let vg: setvar g
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vh: setvar h
  let vy: setvar y
  let cG: class G


  assert |- ( F : RR --> ( 0 [,] +oo ) -> ( S.2 ` F ) e. RR* )

  proof
    cr
    cc0
    cpnf
    cicc
    co
    cF
    wf
    cF
    citg2
    cfv
    vg
    cv
    #
    cF
    cle
    cofr
    wbr
    vx
    cv
    @0
    citg1
    cfv
    wceq
    wa
    vg
    citg1
    cdm
    wrex
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cxr
    vx
    vg
    cF
    @1
    @1
    eqid
    #
    itg2val
    @1
    cxr
    wss
    @2
    cxr
    wcel
    vx
    vg
    cF
    @1
    @3
    itg2lcl
    @1
    supxrcl
    ax-mp
    syl6eqel
end
