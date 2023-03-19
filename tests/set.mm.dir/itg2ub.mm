include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "w3a.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "citg2.mm"
include "wss.mm"
include "eqid.mm"
include "itg2lcl.mm"
include "itg2lr.mm"
include "3adant1.mm"
include "supxrub.mm"
include "sylancr.mm"
include "itg2val.mm"
include "3ad2ant1.mm"
include "breqtrrd.mm"

theorem itg2ub
  let cF: class F
  let cG: class G
  let vg: setvar g
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vh: setvar h
  let vy: setvar y


  assert |- ( ( F : RR --> ( 0 [,] +oo ) /\ G e. dom S.1 /\ G oR <_ F ) -> ( S.1 ` G ) <_ ( S.2 ` F ) )

  proof
    cr
    cc0
    cpnf
    cicc
    co
    cF
    wf
    #
    cG
    citg1
    cdm
    #
    wcel
    #
    cG
    cF
    cle
    cofr
    #
    wbr
    #
    w3a
    #
    cG
    citg1
    cfv
    #
    vg
    cv
    #
    cF
    @3
    wbr
    vx
    cv
    @7
    citg1
    cfv
    wceq
    wa
    vg
    @1
    wrex
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cF
    citg2
    cfv
    #
    cle
    @5
    @8
    cxr
    wss
    @6
    @8
    wcel
    #
    @6
    @9
    cle
    wbr
    vx
    vg
    cF
    @8
    @8
    eqid
    #
    itg2lcl
    @2
    @4
    @11
    @0
    vx
    vg
    cF
    cG
    @8
    @12
    itg2lr
    3adant1
    @8
    @6
    supxrub
    sylancr
    @0
    @2
    @10
    @9
    wceq
    @4
    vx
    vg
    cF
    @8
    @12
    itg2val
    3ad2ant1
    breqtrrd
end
