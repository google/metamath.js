include "wcel.mm"
include "cvv.mm"
include "ctcl.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "elex.mm"
include "cn.mm"
include "cv.mm"
include "crelexp.mm"
include "co.mm"
include "ciun.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "relexpsucnnr.mm"
include "relexpsucnnl.mm"
include "eqtr3d.mm"
include "iuneq2dv.mm"
include "oveq1.mm"
include "iuneq2d.mm"
include "dftrcl3.mm"
include "nnex.mm"
include "ovex.mm"
include "iunex.mm"
include "fvmpt.mm"
include "coeq1d.mm"
include "coiun1.mm"
include "syl6eq.mm"
include "coeq2d.mm"
include "coiun.mm"
include "3eqtr4d.mm"
include "syl.mm"

theorem trclfvcom
  let cR: class R
  let cV: class V
  let vn: setvar n
  let vr: setvar r


  assert |- ( R e. V -> ( ( t+ ` R ) o. R ) = ( R o. ( t+ ` R ) ) )

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
    cR
    ccom
    #
    cR
    @1
    ccom
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
    cR
    ccom
    #
    ciun
    #
    vn
    cn
    cR
    @5
    ccom
    #
    ciun
    #
    @2
    @3
    @0
    vn
    cn
    @6
    @8
    @0
    @4
    cn
    wcel
    wa
    cR
    @4
    c1
    caddc
    co
    crelexp
    co
    @6
    @8
    cR
    @4
    cvv
    relexpsucnnr
    cR
    @4
    cvv
    relexpsucnnl
    eqtr3d
    iuneq2dv
    @0
    @2
    vn
    cn
    @5
    ciun
    #
    cR
    ccom
    @7
    @0
    @1
    @10
    cR
    vr
    cR
    vn
    cn
    vr
    cv
    #
    @4
    crelexp
    co
    #
    ciun
    @10
    cvv
    ctcl
    @11
    cR
    wceq
    vn
    cn
    @12
    @5
    @11
    cR
    @4
    crelexp
    oveq1
    iuneq2d
    vn
    vr
    dftrcl3
    vn
    cn
    @5
    nnex
    cR
    @4
    crelexp
    ovex
    iunex
    fvmpt
    #
    coeq1d
    vn
    @5
    cR
    cn
    coiun1
    syl6eq
    @0
    @3
    cR
    @10
    ccom
    @9
    @0
    @1
    @10
    cR
    @13
    coeq2d
    vn
    cR
    @5
    cn
    coiun
    syl6eq
    3eqtr4d
    syl
end
