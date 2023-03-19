include "cgrp.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "chash.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cod.mm"
include "wral.mm"
include "eqid.mm"
include "oddvds2.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "cz.mm"
include "wb.mm"
include "cn0.mm"
include "hashcl.mm"
include "adantl.mm"
include "nn0zd.mm"
include "gexdvds2.mm"
include "syldan.mm"
include "mpbird.mm"

theorem gexdvds3
  let cE: class E
  let cG: class G
  let cX: class X
  let vx: setvar x
  assume gexcl2.1: |- X = ( Base ` G )
  assume gexcl2.2: |- E = ( gEx ` G )


  assert |- ( ( G e. Grp /\ X e. Fin ) -> E || ( # ` X ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cfn
    wcel
    #
    wa
    #
    cE
    cX
    chash
    cfv
    #
    cdvds
    wbr
    #
    vx
    cv
    #
    cG
    cod
    cfv
    #
    cfv
    @3
    cdvds
    wbr
    #
    vx
    cX
    wral
    #
    @2
    @7
    vx
    cX
    @0
    @1
    @5
    cX
    wcel
    @7
    @5
    cG
    @6
    cX
    gexcl2.1
    @6
    eqid
    #
    oddvds2
    3expa
    ralrimiva
    @0
    @1
    @3
    cz
    wcel
    @4
    @8
    wb
    @2
    @3
    @1
    @3
    cn0
    wcel
    @0
    cX
    hashcl
    adantl
    nn0zd
    vx
    cE
    cG
    @3
    @6
    cX
    gexcl2.1
    gexcl2.2
    @9
    gexdvds2
    syldan
    mpbird
end
