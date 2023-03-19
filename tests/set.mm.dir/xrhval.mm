include "wcel.mm"
include "cvv.mm"
include "cxrh.mm"
include "cfv.mm"
include "cxr.mm"
include "cv.mm"
include "cr.mm"
include "crrh.mm"
include "cpnf.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt.mm"
include "elex.mm"
include "cima.mm"
include "club.mm"
include "cglb.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "syl6eqr.mm"
include "imaeq1d.mm"
include "fveq12d.mm"
include "ifeq12d.mm"
include "mpteq2dv.mm"
include "df-xrh.mm"
include "xrex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem xrhval
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cU: class U
  let cL: class L
  let cV: class V
  let vr: setvar r
  assume xrhval.b: |- B = ( ( RRHom ` R ) " RR )
  assume xrhval.l: |- L = ( glb ` R )
  assume xrhval.u: |- U = ( lub ` R )

  disjoint R x
  disjoint r x
  disjoint R r
  disjoint B r
  disjoint L r
  disjoint U r
  assert |- ( R e. V -> ( RR*Hom ` R ) = ( x e. RR* |-> if ( x e. RR , ( ( RRHom ` R ) ` x ) , if ( x = +oo , ( U ` B ) , ( L ` B ) ) ) ) )

  proof
    cR
    cV
    wcel
    cR
    cvv
    wcel
    cR
    cxrh
    cfv
    vx
    cxr
    vx
    cv
    #
    cr
    wcel
    #
    @0
    cR
    crrh
    cfv
    #
    cfv
    #
    @0
    cpnf
    wceq
    #
    cB
    cU
    cfv
    #
    cB
    cL
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    #
    wceq
    cR
    cV
    elex
    vr
    cR
    vx
    cxr
    @1
    @0
    vr
    cv
    #
    crrh
    cfv
    #
    cfv
    #
    @4
    @11
    cr
    cima
    #
    @10
    club
    cfv
    #
    cfv
    #
    @13
    @10
    cglb
    cfv
    #
    cfv
    #
    cif
    #
    cif
    #
    cmpt
    @9
    cvv
    cxrh
    @10
    cR
    wceq
    #
    vx
    cxr
    @19
    @8
    @20
    @1
    @12
    @3
    @18
    @7
    @20
    @0
    @11
    @2
    @10
    cR
    crrh
    fveq2
    #
    fveq1d
    @20
    @4
    @15
    @5
    @17
    @6
    @20
    @13
    cB
    @14
    cU
    @20
    @14
    cR
    club
    cfv
    cU
    @10
    cR
    club
    fveq2
    xrhval.u
    syl6eqr
    @20
    @13
    @2
    cr
    cima
    cB
    @20
    @11
    @2
    cr
    @21
    imaeq1d
    xrhval.b
    syl6eqr
    #
    fveq12d
    @20
    @13
    cB
    @16
    cL
    @20
    @16
    cR
    cglb
    cfv
    cL
    @10
    cR
    cglb
    fveq2
    xrhval.l
    syl6eqr
    @22
    fveq12d
    ifeq12d
    ifeq12d
    mpteq2dv
    vx
    vr
    df-xrh
    vx
    cxr
    @8
    xrex
    mptex
    fvmpt
    syl
end
