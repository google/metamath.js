include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "wi.mm"
include "grpoidcl.mm"
include "grporcan.mm"
include "3exp2.mm"
include "mpid.mm"
include "pm2.43d.mm"
include "imp.mm"
include "grpolid.mm"
include "eqeq2d.mm"
include "bitr3d.mm"

theorem grpoid
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  let vy: setvar y
  let vz: setvar z
  assume grpinveu.1: |- X = ran G
  assume grpinveu.2: |- U = ( GId ` G )


  assert |- ( ( G e. GrpOp /\ A e. X ) -> ( A = U <-> ( A G A ) = A ) )

  proof
    cG
    cgr
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cA
    cG
    co
    #
    cU
    cA
    cG
    co
    #
    wceq
    #
    cA
    cU
    wceq
    #
    @3
    cA
    wceq
    @0
    @1
    @5
    @6
    wb
    #
    @0
    @1
    @7
    @0
    @1
    cU
    cX
    wcel
    #
    @1
    @7
    wi
    cU
    cG
    cX
    grpinveu.1
    grpinveu.2
    grpoidcl
    @0
    @1
    @8
    @1
    @7
    cA
    cU
    cA
    cG
    cX
    grpinveu.1
    grporcan
    3exp2
    mpid
    pm2.43d
    imp
    @2
    @4
    cA
    @3
    cA
    cU
    cG
    cX
    grpinveu.1
    grpinveu.2
    grpolid
    eqeq2d
    bitr3d
end
