include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cconcat.mm"
include "cxp.mm"
include "cres.mm"
include "frmdplusg.mm"
include "oveqi.mm"
include "ovres.mm"
include "syl5eq.mm"

theorem frmdadd
  let cB: class B
  let c.pl: class .+
  let cI: class I
  let cM: class M
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume frmdbas.m: |- M = ( freeMnd ` I )
  assume frmdbas.b: |- B = ( Base ` M )
  assume frmdplusg.p: |- .+ = ( +g ` M )


  assert |- ( ( X e. B /\ Y e. B ) -> ( X .+ Y ) = ( X ++ Y ) )

  proof
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    cX
    cY
    c.pl
    co
    cX
    cY
    cconcat
    cB
    cB
    cxp
    cres
    #
    co
    cX
    cY
    cconcat
    co
    c.pl
    @0
    cX
    cY
    cB
    c.pl
    cI
    cM
    frmdbas.m
    frmdbas.b
    frmdplusg.p
    frmdplusg
    oveqi
    cX
    cY
    cB
    cB
    cconcat
    ovres
    syl5eq
end
