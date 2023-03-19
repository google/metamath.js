include "crp.mm"
include "cv.mm"
include "rpcn.mm"
include "rpne0.mm"
include "rpmulcl.mm"
include "1rp.mm"
include "rpreccl.mm"
include "cnmsubglem.mm"

theorem rpmsubg
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  assume cnmgpabl.m: |- M = ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) )


  assert |- RR+ e. ( SubGrp ` M )

  proof
    vx
    vy
    crp
    cM
    cnmgpabl.m
    vx
    cv
    #
    rpcn
    @0
    rpne0
    @0
    vy
    cv
    rpmulcl
    1rp
    @0
    rpreccl
    cnmsubglem
end
