include "cv.mm"
include "cdm.mm"
include "wceq.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "ccnv.mm"
include "wfun.mm"
include "cuni.mm"
include "cima.mm"
include "cdif.mm"
include "cres.mm"
include "dfdm4.mm"
include "difss.mm"
include "sseq2.mm"
include "mpbiri.mm"
include "ssdmres.mm"
include "sylib.mm"
include "syl5reqr.mm"
include "funcnvres.mm"
include "sbthlem3.mm"
include "reseq2d.mm"
include "sylan9eqr.mm"
include "rneqd.mm"
include "sylan9eq.mm"
include "anassrs.mm"
include "df-ima.mm"
include "syl6reqr.mm"

theorem sbthlem4
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  assume sbthlem.1: |- A e. _V
  assume sbthlem.2: |- D = { x | ( x C_ A /\ ( g " ( B \ ( f " x ) ) ) C_ ( A \ x ) ) }

  disjoint A x
  disjoint B x
  disjoint D x
  disjoint f x
  disjoint g x
  assert |- ( ( ( dom g = B /\ ran g C_ A ) /\ Fun `' g ) -> ( `' g " ( A \ U. D ) ) = ( B \ ( f " U. D ) ) )

  proof
    vg
    cv
    #
    cdm
    #
    cB
    wceq
    #
    @0
    crn
    cA
    wss
    #
    wa
    @0
    ccnv
    #
    wfun
    #
    wa
    cB
    vf
    cv
    cD
    cuni
    #
    cima
    #
    cdif
    #
    @4
    cA
    @6
    cdif
    #
    cres
    #
    crn
    #
    @4
    @9
    cima
    @2
    @3
    @5
    @8
    @11
    wceq
    @2
    @3
    @5
    wa
    #
    @8
    @0
    @8
    cres
    #
    ccnv
    #
    crn
    #
    @11
    @2
    @15
    @13
    cdm
    #
    @8
    @13
    dfdm4
    @2
    @8
    @1
    wss
    #
    @16
    @8
    wceq
    @2
    @17
    @8
    cB
    wss
    cB
    @7
    difss
    @1
    cB
    @8
    sseq2
    mpbiri
    @8
    @0
    ssdmres
    sylib
    syl5reqr
    @12
    @14
    @10
    @5
    @3
    @14
    @4
    @0
    @8
    cima
    #
    cres
    @10
    @8
    @0
    funcnvres
    @3
    @18
    @9
    @4
    vx
    cA
    cB
    cD
    vf
    vg
    sbthlem.1
    sbthlem.2
    sbthlem3
    reseq2d
    sylan9eqr
    rneqd
    sylan9eq
    anassrs
    @4
    @9
    df-ima
    syl6reqr
end
