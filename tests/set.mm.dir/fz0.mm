include "cz.mm"
include "wnel.mm"
include "wo.mm"
include "wcel.mm"
include "wn.mm"
include "cfz.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "df-nel.mm"
include "orbi12i.mm"
include "wa.mm"
include "ianor.mm"
include "cxp.mm"
include "cpw.mm"
include "fzf.mm"
include "fdmi.mm"
include "ndmov.mm"
include "sylbir.mm"
include "sylbi.mm"

theorem fz0
  let cM: class M
  let cN: class N


  assert |- ( ( M e/ ZZ \/ N e/ ZZ ) -> ( M ... N ) = (/) )

  proof
    cM
    cz
    wnel
    #
    cN
    cz
    wnel
    #
    wo
    cM
    cz
    wcel
    #
    wn
    #
    cN
    cz
    wcel
    #
    wn
    #
    wo
    #
    cM
    cN
    cfz
    co
    c0
    wceq
    #
    @0
    @3
    @1
    @5
    cM
    cz
    df-nel
    cN
    cz
    df-nel
    orbi12i
    @6
    @2
    @4
    wa
    wn
    @7
    @2
    @4
    ianor
    cM
    cN
    cz
    cfz
    cz
    cz
    cxp
    cz
    cpw
    cfz
    fzf
    fdmi
    ndmov
    sylbir
    sylbi
end
