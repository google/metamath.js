include "crg.mm"
include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cgrp.mm"
include "eqid.mm"
include "unitgrp.mm"
include "unitgrpbas.mm"
include "invrfval.mm"
include "grpinvcl.mm"
include "sylan.mm"

theorem unitinvcl
  let cR: class R
  let cU: class U
  let cI: class I
  let cX: class X
  assume unitinvcl.1: |- U = ( Unit ` R )
  assume unitinvcl.2: |- I = ( invr ` R )


  assert |- ( ( R e. Ring /\ X e. U ) -> ( I ` X ) e. U )

  proof
    cR
    crg
    wcel
    cR
    cmgp
    cfv
    cU
    cress
    co
    #
    cgrp
    wcel
    cX
    cU
    wcel
    cX
    cI
    cfv
    cU
    wcel
    cR
    cU
    @0
    unitinvcl.1
    @0
    eqid
    #
    unitgrp
    cU
    @0
    cI
    cX
    cR
    cU
    @0
    unitinvcl.1
    @1
    unitgrpbas
    cR
    cU
    @0
    cI
    unitinvcl.1
    @1
    unitinvcl.2
    invrfval
    grpinvcl
    sylan
end
