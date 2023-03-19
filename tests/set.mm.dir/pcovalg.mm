include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "wcel.mm"
include "cpco.mm"
include "cfv.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "pcoval.mm"
include "fveq1d.mm"
include "wceq.mm"
include "breq1.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "ifbieq12d.mm"
include "eqid.mm"
include "fvex.mm"
include "ifex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem pcovalg
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cH: class H
  let vj: setvar j
  assume pcoval.2: |- ( ph -> F e. ( II Cn J ) )
  assume pcoval.3: |- ( ph -> G e. ( II Cn J ) )


  assert |- ( ( ph /\ X e. ( 0 [,] 1 ) ) -> ( ( F ( *p ` J ) G ) ` X ) = if ( X <_ ( 1 / 2 ) , ( F ` ( 2 x. X ) ) , ( G ` ( ( 2 x. X ) - 1 ) ) ) )

  proof
    wph
    cX
    cc0
    c1
    cicc
    co
    #
    wcel
    cX
    cF
    cG
    cJ
    cpco
    cfv
    co
    #
    cfv
    cX
    vx
    @0
    vx
    cv
    #
    c1
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    c2
    @2
    cmul
    co
    #
    cF
    cfv
    #
    @5
    c1
    cmin
    co
    #
    cG
    cfv
    #
    cif
    #
    cmpt
    #
    cfv
    cX
    @3
    cle
    wbr
    #
    c2
    cX
    cmul
    co
    #
    cF
    cfv
    #
    @12
    c1
    cmin
    co
    #
    cG
    cfv
    #
    cif
    #
    wph
    cX
    @1
    @10
    wph
    vx
    cF
    cG
    cJ
    pcoval.2
    pcoval.3
    pcoval
    fveq1d
    vx
    cX
    @9
    @16
    @0
    @10
    @2
    cX
    wceq
    #
    @4
    @11
    @6
    @8
    @13
    @15
    @2
    cX
    @3
    cle
    breq1
    @17
    @5
    @12
    cF
    @2
    cX
    c2
    cmul
    oveq2
    #
    fveq2d
    @17
    @7
    @14
    cG
    @17
    @5
    @12
    c1
    cmin
    @18
    oveq1d
    fveq2d
    ifbieq12d
    @10
    eqid
    @11
    @13
    @15
    @12
    cF
    fvex
    @14
    cG
    fvex
    ifex
    fvmpt
    sylan9eq
end
