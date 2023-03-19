include "cv.mm"
include "cdm.mm"
include "wceq.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "cuni.mm"
include "cdif.mm"
include "cun.mm"
include "cin.mm"
include "cima.mm"
include "sbthlem1.mm"
include "difss.mm"
include "sstri.mm"
include "sseq2.mm"
include "mpbiri.mm"
include "dfss.mm"
include "sylib.mm"
include "uneq1d.mm"
include "sbthlem3.mm"
include "imassrn.mm"
include "syl6eqssr.mm"
include "uneq2d.mm"
include "sylan9eq.mm"
include "cres.mm"
include "ccnv.mm"
include "dmeqi.mm"
include "dmun.mm"
include "dmres.mm"
include "df-rn.mm"
include "eqcomi.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "uneq12i.mm"
include "syl6reqr.mm"
include "undif.mm"
include "mpbi.mm"
include "syl6eq.mm"

theorem sbthlem5
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
  assert |- ( ( dom f = A /\ ran g C_ A ) -> dom H = A )

  proof
    vf
    cv
    #
    cdm
    #
    cA
    wceq
    #
    vg
    cv
    #
    crn
    #
    cA
    wss
    #
    wa
    #
    cH
    cdm
    #
    cD
    cuni
    #
    cA
    @8
    cdif
    #
    cun
    #
    cA
    @6
    @10
    @8
    @1
    cin
    #
    @9
    @4
    cin
    #
    cun
    #
    @7
    @2
    @5
    @10
    @11
    @9
    cun
    @13
    @2
    @8
    @11
    @9
    @2
    @8
    @1
    wss
    #
    @8
    @11
    wceq
    @2
    @14
    @8
    cA
    wss
    #
    @8
    cA
    @3
    cB
    @0
    @8
    cima
    cdif
    #
    cima
    #
    cdif
    cA
    vx
    cA
    cB
    cD
    vf
    vg
    sbthlem.1
    sbthlem.2
    sbthlem1
    cA
    @17
    difss
    sstri
    #
    @1
    cA
    @8
    sseq2
    mpbiri
    @8
    @1
    dfss
    sylib
    uneq1d
    @5
    @9
    @12
    @11
    @5
    @9
    @4
    wss
    @9
    @12
    wceq
    @5
    @9
    @17
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
    @3
    @16
    imassrn
    syl6eqssr
    @9
    @4
    dfss
    sylib
    uneq2d
    sylan9eq
    @7
    @0
    @8
    cres
    #
    @3
    ccnv
    #
    @9
    cres
    #
    cun
    #
    cdm
    #
    @13
    cH
    @22
    sbthlem.3
    dmeqi
    @23
    @19
    cdm
    #
    @21
    cdm
    #
    cun
    @13
    @19
    @21
    dmun
    @24
    @11
    @25
    @12
    @0
    @8
    dmres
    @25
    @9
    @20
    cdm
    #
    cin
    @12
    @20
    @9
    dmres
    @26
    @4
    @9
    @4
    @26
    @3
    df-rn
    eqcomi
    ineq2i
    eqtri
    uneq12i
    eqtri
    eqtri
    syl6reqr
    @15
    @10
    cA
    wceq
    @18
    @8
    cA
    undif
    mpbi
    syl6eq
end
