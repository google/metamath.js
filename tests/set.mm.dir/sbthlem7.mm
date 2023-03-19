include "cv.mm"
include "wfun.mm"
include "ccnv.mm"
include "wa.mm"
include "cuni.mm"
include "cres.mm"
include "cdif.mm"
include "cun.mm"
include "funres.mm"
include "cdm.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "ssrin.mm"
include "ax-mp.mm"
include "sslin.mm"
include "sstri.mm"
include "disjdif.mm"
include "sseqtri.mm"
include "ss0.mm"
include "funun.mm"
include "mpan2.mm"
include "syl2an.mm"
include "funeqi.mm"
include "sylibr.mm"

theorem sbthlem7
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
  assert |- ( ( Fun f /\ Fun `' g ) -> Fun H )

  proof
    vf
    cv
    #
    wfun
    #
    vg
    cv
    ccnv
    #
    wfun
    #
    wa
    @0
    cD
    cuni
    #
    cres
    #
    @2
    cA
    @4
    cdif
    #
    cres
    #
    cun
    #
    wfun
    #
    cH
    wfun
    @1
    @5
    wfun
    #
    @7
    wfun
    #
    @9
    @3
    @4
    @0
    funres
    @6
    @2
    funres
    @10
    @11
    wa
    @5
    cdm
    #
    @7
    cdm
    #
    cin
    #
    c0
    wceq
    #
    @9
    @14
    c0
    wss
    @15
    @14
    @4
    @6
    cin
    #
    c0
    @14
    @4
    @13
    cin
    #
    @16
    @12
    @4
    wss
    @14
    @17
    wss
    @12
    @4
    @0
    cdm
    #
    cin
    @4
    @0
    @4
    dmres
    @4
    @18
    inss1
    eqsstri
    @12
    @4
    @13
    ssrin
    ax-mp
    @13
    @6
    wss
    @17
    @16
    wss
    @13
    @6
    @2
    cdm
    #
    cin
    @6
    @2
    @6
    dmres
    @6
    @19
    inss1
    eqsstri
    @13
    @6
    @4
    sslin
    ax-mp
    sstri
    @4
    cA
    disjdif
    sseqtri
    @14
    ss0
    ax-mp
    @5
    @7
    funun
    mpan2
    syl2an
    cH
    @8
    sbthlem.3
    funeqi
    sylibr
end
