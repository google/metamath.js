include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cplusg.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "cress.mm"
include "co.mm"
include "csubg.mm"
include "grpissubg.mm"
include "imp.mm"
include "w3a.mm"
include "wb.mm"
include "ibar.mm"
include "ad2ant2r.mm"
include "df-3an.mm"
include "syl6bbr.mm"
include "issubg.mm"
include "mpbird.mm"
include "ex.mm"

theorem resgrpisgrp
  let cB: class B
  let cS: class S
  let cG: class G
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume grpissubg.b: |- B = ( Base ` G )
  assume grpissubg.s: |- S = ( Base ` H )


  assert |- ( ( G e. Grp /\ H e. Grp ) -> ( ( S C_ B /\ ( +g ` H ) = ( ( +g ` G ) |` ( S X. S ) ) ) -> ( G |`s S ) e. Grp ) )

  proof
    cG
    cgrp
    wcel
    #
    cH
    cgrp
    wcel
    #
    wa
    #
    cS
    cB
    wss
    #
    cH
    cplusg
    cfv
    cG
    cplusg
    cfv
    cS
    cS
    cxp
    cres
    wceq
    #
    wa
    #
    cG
    cS
    cress
    co
    cgrp
    wcel
    #
    @2
    @5
    wa
    #
    @6
    cS
    cG
    csubg
    cfv
    wcel
    #
    @2
    @5
    @8
    cB
    cS
    cG
    cH
    grpissubg.b
    grpissubg.s
    grpissubg
    imp
    @7
    @6
    @0
    @3
    @6
    w3a
    #
    @8
    @7
    @6
    @0
    @3
    wa
    #
    @6
    wa
    #
    @9
    @0
    @3
    @6
    @11
    wb
    @1
    @4
    @10
    @6
    ibar
    ad2ant2r
    @0
    @3
    @6
    df-3an
    syl6bbr
    cB
    cS
    cG
    grpissubg.b
    issubg
    syl6bbr
    mpbird
    ex
end
