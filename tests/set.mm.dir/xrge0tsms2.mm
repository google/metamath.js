include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "ctsu.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "cres.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "csn.mm"
include "c1o.mm"
include "cen.mm"
include "simpl.mm"
include "simpr.mm"
include "eqid.mm"
include "xrge0tsms.mm"
include "xrltso.mm"
include "supex.mm"
include "ensn1.mm"
include "syl6eqbr.mm"

theorem xrge0tsms2
  let cA: class A
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume xrge0tsms2.g: |- G = ( RR*s |`s ( 0 [,] +oo ) )


  assert |- ( ( A e. V /\ F : A --> ( 0 [,] +oo ) ) -> ( G tsums F ) ~~ 1o )

  proof
    cA
    cV
    wcel
    #
    cA
    cc0
    cpnf
    cicc
    co
    cF
    wf
    #
    wa
    #
    cG
    cF
    ctsu
    co
    vx
    cA
    cpw
    cfn
    cin
    cG
    cF
    vx
    cv
    cres
    cgsu
    co
    cmpt
    crn
    #
    cxr
    clt
    csup
    #
    csn
    c1o
    cen
    @2
    cA
    @4
    cF
    cG
    cV
    vx
    xrge0tsms2.g
    @0
    @1
    simpl
    @0
    @1
    simpr
    @4
    eqid
    xrge0tsms
    @4
    cxr
    @3
    clt
    xrltso
    supex
    ensn1
    syl6eqbr
end
