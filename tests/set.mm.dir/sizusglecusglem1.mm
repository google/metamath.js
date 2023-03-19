include "cusgr.mm"
include "wcel.mm"
include "ccusgr.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "wf1.mm"
include "wss.mm"
include "wf1o.mm"
include "f1oi.mm"
include "f1of1.mm"
include "ax-mp.mm"
include "usgredgsscusgredg.mm"
include "f1ss.mm"
include "sylancr.mm"

theorem sizusglecusglem1
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let ve: setvar e
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  assume fusgrmaxsize.v: |- V = ( Vtx ` G )
  assume fusgrmaxsize.e: |- E = ( Edg ` G )
  assume usgrsscusgra.h: |- V = ( Vtx ` H )
  assume usgrsscusgra.f: |- F = ( Edg ` H )


  assert |- ( ( G e. USGraph /\ H e. ComplUSGraph ) -> ( _I |` E ) : E -1-1-> F )

  proof
    cG
    cusgr
    wcel
    cH
    ccusgr
    wcel
    wa
    cE
    cE
    cid
    cE
    cres
    #
    wf1
    #
    cE
    cF
    wss
    cE
    cF
    @0
    wf1
    cE
    cE
    @0
    wf1o
    @1
    cE
    f1oi
    cE
    cE
    @0
    f1of1
    ax-mp
    cE
    cF
    cG
    cH
    cV
    fusgrmaxsize.v
    fusgrmaxsize.e
    usgrsscusgra.h
    usgrsscusgra.f
    usgredgsscusgredg
    cE
    cE
    cF
    @0
    f1ss
    sylancr
end
