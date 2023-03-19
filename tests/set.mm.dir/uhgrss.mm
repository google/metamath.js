include "cuhgr.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "uhgrf.mm"
include "ffvelrnda.mm"
include "eldifad.mm"
include "elpwid.mm"

theorem uhgrss
  let cE: class E
  let cF: class F
  let cG: class G
  let cV: class V
  assume uhgrf.v: |- V = ( Vtx ` G )
  assume uhgrf.e: |- E = ( iEdg ` G )


  assert |- ( ( G e. UHGraph /\ F e. dom E ) -> ( E ` F ) C_ V )

  proof
    cG
    cuhgr
    wcel
    #
    cF
    cE
    cdm
    #
    wcel
    wa
    #
    cF
    cE
    cfv
    #
    cV
    @2
    @3
    cV
    cpw
    #
    c0
    csn
    #
    @0
    @1
    @4
    @5
    cdif
    cF
    cE
    cE
    cG
    cV
    uhgrf.v
    uhgrf.e
    uhgrf
    ffvelrnda
    eldifad
    elpwid
end
