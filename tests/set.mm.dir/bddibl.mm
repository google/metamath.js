include "cmbf.mm"
include "wcel.mm"
include "cdm.mm"
include "cvol.mm"
include "cfv.mm"
include "cr.mm"
include "cv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "w3a.mm"
include "c1.mm"
include "csn.mm"
include "cxp.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "cibl.mm"
include "mbfdm.mm"
include "3ad2ant1.mm"
include "cc.mm"
include "wf.mm"
include "wfn.mm"
include "mbff.mm"
include "ffn.mm"
include "syl.mm"
include "1cnd.mm"
include "fnconstg.mm"
include "wa.mm"
include "eqidd.mm"
include "wceq.mm"
include "1ex.mm"
include "fvconst2.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "mulid1d.mm"
include "offveq.mm"
include "simp2.mm"
include "iblconst.mm"
include "syl3anc.mm"
include "bddmulibl.mm"
include "syld3an2.mm"
include "eqeltrrd.mm"

theorem bddibl
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cA: class A
  let cB: class B
  let vz: setvar z
  let cG: class G

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint y z
  disjoint F z
  disjoint G x
  disjoint G y
  disjoint G z
  assert |- ( ( F e. MblFn /\ ( vol ` dom F ) e. RR /\ E. x e. RR A. y e. dom F ( abs ` ( F ` y ) ) <_ x ) -> F e. L^1 )

  proof
    cF
    cmbf
    wcel
    #
    cF
    cdm
    #
    cvol
    cfv
    cr
    wcel
    #
    vy
    cv
    cF
    cfv
    cabs
    cfv
    vx
    cv
    cle
    wbr
    vy
    @1
    wral
    vx
    cr
    wrex
    #
    w3a
    #
    cF
    @1
    c1
    csn
    cxp
    #
    cmul
    cof
    co
    #
    cF
    cibl
    @4
    vz
    @1
    vz
    cv
    #
    cF
    cfv
    #
    c1
    cmul
    cF
    @5
    cF
    cvol
    cdm
    #
    @0
    @2
    @1
    @9
    wcel
    #
    @3
    cF
    mbfdm
    3ad2ant1
    #
    @4
    @1
    cc
    cF
    wf
    #
    cF
    @1
    wfn
    @0
    @2
    @12
    @3
    cF
    mbff
    3ad2ant1
    #
    @1
    cc
    cF
    ffn
    syl
    #
    @4
    c1
    cc
    wcel
    #
    @5
    @1
    wfn
    @4
    1cnd
    #
    @1
    c1
    cc
    fnconstg
    syl
    @14
    @4
    @7
    @1
    wcel
    #
    wa
    #
    @8
    eqidd
    @17
    @7
    @5
    cfv
    c1
    wceq
    @4
    @1
    c1
    @7
    1ex
    fvconst2
    adantl
    @18
    @8
    @4
    @1
    cc
    @7
    cF
    @13
    ffvelrnda
    mulid1d
    offveq
    @0
    @5
    cibl
    wcel
    #
    @2
    @3
    @6
    cibl
    wcel
    @4
    @10
    @2
    @15
    @19
    @11
    @0
    @2
    @3
    simp2
    @16
    @1
    c1
    iblconst
    syl3anc
    vx
    vy
    cF
    @5
    bddmulibl
    syld3an2
    eqeltrrd
end
