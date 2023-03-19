include "wcel.mm"
include "cvv.mm"
include "ctcl.mm"
include "cfv.mm"
include "ccnv.mm"
include "wceq.mm"
include "elex.mm"
include "cn.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "wral.mm"
include "cn0.mm"
include "nnnn0.mm"
include "relexpcnv.mm"
include "sylan.mm"
include "expcom.mm"
include "ralrimiv.mm"
include "iuneq2.mm"
include "syl.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "dftrcl3.mm"
include "nnex.mm"
include "ovex.mm"
include "iunex.mm"
include "fvmpt.mm"
include "cnveqd.mm"
include "cnviun.mm"
include "syl6eq.mm"
include "cnvexg.mm"
include "3eqtr4d.mm"

theorem cnvtrclfv
  let cR: class R
  let cV: class V
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s


  assert |- ( R e. V -> `' ( t+ ` R ) = ( t+ ` `' R ) )

  proof
    cR
    cV
    wcel
    cR
    cvv
    wcel
    #
    cR
    ctcl
    cfv
    #
    ccnv
    #
    cR
    ccnv
    #
    ctcl
    cfv
    #
    wceq
    cR
    cV
    elex
    @0
    vn
    cn
    cR
    vn
    cv
    #
    crelexp
    co
    #
    ccnv
    #
    ciun
    #
    vn
    cn
    @3
    @5
    crelexp
    co
    #
    ciun
    #
    @2
    @4
    @0
    @7
    @9
    wceq
    #
    vn
    cn
    wral
    @8
    @10
    wceq
    @0
    @11
    vn
    cn
    @5
    cn
    wcel
    #
    @0
    @11
    @12
    @5
    cn0
    wcel
    @0
    @11
    @5
    nnnn0
    cR
    @5
    cvv
    relexpcnv
    sylan
    expcom
    ralrimiv
    vn
    cn
    @7
    @9
    iuneq2
    syl
    @0
    @2
    vn
    cn
    @6
    ciun
    #
    ccnv
    @8
    @0
    @1
    @13
    vr
    cR
    vn
    cn
    vr
    cv
    #
    @5
    crelexp
    co
    #
    ciun
    @13
    cvv
    ctcl
    @14
    cR
    wceq
    vn
    cn
    @15
    @6
    @14
    cR
    @5
    crelexp
    oveq1
    iuneq2d
    vn
    vr
    dftrcl3
    vn
    cn
    @6
    nnex
    cR
    @5
    crelexp
    ovex
    iunex
    fvmpt
    cnveqd
    vn
    cn
    @6
    cnviun
    syl6eq
    @0
    @3
    cvv
    wcel
    @4
    @10
    wceq
    cR
    cvv
    cnvexg
    vs
    @3
    vn
    cn
    vs
    cv
    #
    @5
    crelexp
    co
    #
    ciun
    @10
    cvv
    ctcl
    @16
    @3
    wceq
    vn
    cn
    @17
    @9
    @16
    @3
    @5
    crelexp
    oveq1
    iuneq2d
    vn
    vs
    dftrcl3
    vn
    cn
    @9
    nnex
    @3
    @5
    crelexp
    ovex
    iunex
    fvmpt
    syl
    3eqtr4d
    syl
end
