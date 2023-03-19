include "cdm.mm"
include "wrel.mm"
include "ctpos.mm"
include "cres.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cuni.mm"
include "cmpt.mm"
include "ccom.mm"
include "dmtpos.mm"
include "reseq2d.mm"
include "wceq.mm"
include "reltpos.mm"
include "resdm.mm"
include "ax-mp.mm"
include "c0.mm"
include "cun.mm"
include "df-tpos.mm"
include "reseq1i.mm"
include "resco.mm"
include "wss.mm"
include "ssun1.mm"
include "resmpt.mm"
include "coeq2i.mm"
include "3eqtri.mm"
include "3eqtr3g.mm"

theorem dftpos2
  let vx: setvar x
  let cF: class F
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G

  disjoint F x
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G x
  assert |- ( Rel dom F -> tpos F = ( F o. ( x e. `' dom F |-> U. `' { x } ) ) )

  proof
    cF
    cdm
    #
    wrel
    #
    cF
    ctpos
    #
    @2
    cdm
    #
    cres
    #
    @2
    @0
    ccnv
    #
    cres
    #
    @2
    cF
    vx
    @5
    vx
    cv
    csn
    ccnv
    cuni
    #
    cmpt
    #
    ccom
    #
    @1
    @3
    @5
    @2
    cF
    dmtpos
    reseq2d
    @2
    wrel
    @4
    @2
    wceq
    cF
    reltpos
    @2
    resdm
    ax-mp
    @6
    cF
    vx
    @5
    c0
    csn
    #
    cun
    #
    @7
    cmpt
    #
    ccom
    #
    @5
    cres
    cF
    @12
    @5
    cres
    #
    ccom
    @9
    @2
    @13
    @5
    vx
    cF
    df-tpos
    reseq1i
    cF
    @12
    @5
    resco
    @14
    @8
    cF
    @5
    @11
    wss
    @14
    @8
    wceq
    @5
    @10
    ssun1
    vx
    @11
    @5
    @7
    resmpt
    ax-mp
    coeq2i
    3eqtri
    3eqtr3g
end
