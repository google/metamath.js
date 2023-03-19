include "cmgm.mm"
include "wcel.mm"
include "c0.mm"
include "wnel.mm"
include "wa.mm"
include "crn.mm"
include "cxp.mm"
include "cres.mm"
include "wceq.mm"
include "wf.mm"
include "wss.mm"
include "wi.mm"
include "mgmplusf.mm"
include "frn.mm"
include "ssel.mm"
include "nelcon3d.mm"
include "3syl.mm"
include "imp.mm"
include "plusfreseq.mm"
include "syl.mm"

theorem mgmplusfreseq
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let cM: class M
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume plusfreseq.1: |- B = ( Base ` M )
  assume plusfreseq.2: |- .+ = ( +g ` M )
  assume plusfreseq.3: |- .+^ = ( +f ` M )


  assert |- ( ( M e. Mgm /\ (/) e/ B ) -> ( .+ |` ( B X. B ) ) = .+^ )

  proof
    cM
    cmgm
    wcel
    #
    c0
    cB
    wnel
    #
    wa
    c0
    c.pd
    crn
    #
    wnel
    #
    c.pl
    cB
    cB
    cxp
    #
    cres
    c.pd
    wceq
    @0
    @1
    @3
    @0
    @4
    cB
    c.pd
    wf
    @2
    cB
    wss
    #
    @1
    @3
    wi
    cB
    c.pd
    cM
    plusfreseq.1
    plusfreseq.3
    mgmplusf
    @4
    cB
    c.pd
    frn
    @5
    c0
    @2
    c0
    cB
    @2
    cB
    c0
    ssel
    nelcon3d
    3syl
    imp
    cB
    c.pl
    c.pd
    cM
    plusfreseq.1
    plusfreseq.2
    plusfreseq.3
    plusfreseq
    syl
end
