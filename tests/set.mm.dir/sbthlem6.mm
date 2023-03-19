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
include "cun.mm"
include "cres.mm"
include "df-ima.mm"
include "sbthlem4.mm"
include "syl5reqr.mm"
include "uneq2d.mm"
include "rnun.mm"
include "rneqi.mm"
include "uneq1i.mm"
include "3eqtr4i.mm"
include "syl6reqr.mm"
include "wi.mm"
include "imassrn.mm"
include "sstr2.mm"
include "ax-mp.mm"
include "undif.mm"
include "sylib.mm"
include "sylan9eqr.mm"

theorem sbthlem6
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  assume sbthlem.1: |- A e. _V
  assume sbthlem.2: |- D = { x | ( x C_ A /\ ( g " ( B \ ( f " x ) ) ) C_ ( A \ x ) ) }
  assume sbthlem.3: |- H = ( ( f |` U. D ) u. ( `' g |` ( A \ U. D ) ) )

  disjoint H x
  disjoint A x
  disjoint B x
  disjoint D x
  disjoint f x
  disjoint g x
  assert |- ( ( ran f C_ B /\ ( ( dom g = B /\ ran g C_ A ) /\ Fun `' g ) ) -> ran H = B )

  proof
    vg
    cv
    #
    cdm
    cB
    wceq
    @0
    crn
    cA
    wss
    wa
    @0
    ccnv
    #
    wfun
    wa
    #
    vf
    cv
    #
    crn
    #
    cB
    wss
    #
    cH
    crn
    #
    @3
    cD
    cuni
    #
    cima
    #
    cB
    @8
    cdif
    #
    cun
    #
    cB
    @2
    @10
    @8
    @1
    cA
    @7
    cdif
    #
    cres
    #
    crn
    #
    cun
    #
    @6
    @2
    @9
    @13
    @8
    @2
    @13
    @1
    @11
    cima
    @9
    @1
    @11
    df-ima
    vx
    cA
    cB
    cD
    vf
    vg
    sbthlem.1
    sbthlem.2
    sbthlem4
    syl5reqr
    uneq2d
    @3
    @7
    cres
    #
    @12
    cun
    #
    crn
    @15
    crn
    #
    @13
    cun
    @6
    @14
    @15
    @12
    rnun
    cH
    @16
    sbthlem.3
    rneqi
    @8
    @17
    @13
    @3
    @7
    df-ima
    uneq1i
    3eqtr4i
    syl6reqr
    @5
    @8
    cB
    wss
    #
    @10
    cB
    wceq
    @8
    @4
    wss
    @5
    @18
    wi
    @3
    @7
    imassrn
    @8
    @4
    cB
    sstr2
    ax-mp
    @8
    cB
    undif
    sylib
    sylan9eqr
end
