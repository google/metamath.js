include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "cv.mm"
include "cmin.mm"
include "cfv.mm"
include "cmpt.mm"
include "cpco.mm"
include "csn.mm"
include "cxp.mm"
include "cphtpc.mm"
include "wbr.mm"
include "wceq.mm"
include "pcorevcl.mm"
include "simp1d.mm"
include "eqid.mm"
include "pcorev.mm"
include "syl.mm"
include "cuni.mm"
include "iiuni.mm"
include "cnf.mm"
include "feqmptd.mm"
include "iirev.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "cc.mm"
include "ax-1cn.mm"
include "cr.mm"
include "unitssre.mm"
include "sseli.mm"
include "recnd.mm"
include "nncan.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "syl6reqr.mm"
include "oveq1d.mm"
include "simp3d.mm"
include "sneqd.mm"
include "xpeq2d.mm"
include "syl6eqr.mm"
include "3brtr3d.mm"

theorem pcorev2
  let vx: setvar x
  let cP: class P
  let cF: class F
  let cG: class G
  let cJ: class J
  let vy: setvar y
  assume pcorev2.1: |- G = ( x e. ( 0 [,] 1 ) |-> ( F ` ( 1 - x ) ) )
  assume pcorev2.2: |- P = ( ( 0 [,] 1 ) X. { ( F ` 0 ) } )

  disjoint F x
  disjoint J x
  disjoint x y
  disjoint F y
  disjoint G y
  disjoint J y
  assert |- ( F e. ( II Cn J ) -> ( F ( *p ` J ) G ) ( ~=ph ` J ) P )

  proof
    cF
    cii
    cJ
    ccn
    co
    #
    wcel
    #
    vy
    cc0
    c1
    cicc
    co
    #
    c1
    vy
    cv
    #
    cmin
    co
    #
    cG
    cfv
    #
    cmpt
    #
    cG
    cJ
    cpco
    cfv
    #
    co
    #
    @2
    c1
    cG
    cfv
    #
    csn
    #
    cxp
    #
    cF
    cG
    @7
    co
    cP
    cJ
    cphtpc
    cfv
    #
    @1
    cG
    @0
    wcel
    #
    @8
    @11
    @12
    wbr
    @1
    @13
    cc0
    cG
    cfv
    c1
    cF
    cfv
    wceq
    #
    @9
    cc0
    cF
    cfv
    #
    wceq
    #
    vx
    cF
    cG
    cJ
    pcorev2.1
    pcorevcl
    #
    simp1d
    vy
    @11
    cG
    @6
    cJ
    @6
    eqid
    @11
    eqid
    pcorev
    syl
    @1
    @6
    cF
    cG
    @7
    @1
    cF
    vy
    @2
    @3
    cF
    cfv
    #
    cmpt
    @6
    @1
    vy
    @2
    cJ
    cuni
    #
    cF
    cF
    cii
    cJ
    @2
    @19
    iiuni
    @19
    eqid
    cnf
    feqmptd
    vy
    @2
    @5
    @18
    @3
    @2
    wcel
    #
    @5
    c1
    @4
    cmin
    co
    #
    cF
    cfv
    #
    @18
    @20
    @4
    @2
    wcel
    @5
    @22
    wceq
    @3
    iirev
    vx
    @4
    c1
    vx
    cv
    #
    cmin
    co
    #
    cF
    cfv
    @22
    @2
    cG
    @23
    @4
    wceq
    @24
    @21
    cF
    @23
    @4
    c1
    cmin
    oveq2
    fveq2d
    pcorev2.1
    @21
    cF
    fvex
    fvmpt
    syl
    @20
    @21
    @3
    cF
    @20
    c1
    cc
    wcel
    @3
    cc
    wcel
    @21
    @3
    wceq
    ax-1cn
    @20
    @3
    @2
    cr
    @3
    unitssre
    sseli
    recnd
    c1
    @3
    nncan
    sylancr
    fveq2d
    eqtrd
    mpteq2ia
    syl6reqr
    oveq1d
    @1
    @11
    @2
    @15
    csn
    #
    cxp
    cP
    @1
    @10
    @25
    @2
    @1
    @9
    @15
    @1
    @13
    @14
    @16
    @17
    simp3d
    sneqd
    xpeq2d
    pcorev2.2
    syl6eqr
    3brtr3d
end
