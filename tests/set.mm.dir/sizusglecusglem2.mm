include "cusgr.mm"
include "wcel.mm"
include "ccusgr.mm"
include "cfn.mm"
include "w3a.mm"
include "cusgrfi.mm"
include "3adant1.mm"
include "wi.mm"
include "wa.mm"
include "cedg.mm"
include "cfv.mm"
include "cfusgr.mm"
include "isfusgr.mm"
include "fusgrfis.mm"
include "sylbir.mm"
include "syl5eqel.mm"
include "ex.mm"
include "3ad2ant1.mm"
include "mpd.mm"

theorem sizusglecusglem2
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


  assert |- ( ( G e. USGraph /\ H e. ComplUSGraph /\ F e. Fin ) -> E e. Fin )

  proof
    cG
    cusgr
    wcel
    #
    cH
    ccusgr
    wcel
    #
    cF
    cfn
    wcel
    #
    w3a
    cV
    cfn
    wcel
    #
    cE
    cfn
    wcel
    #
    @1
    @2
    @3
    @0
    cF
    cH
    cV
    usgrsscusgra.h
    usgrsscusgra.f
    cusgrfi
    3adant1
    @0
    @1
    @3
    @4
    wi
    @2
    @0
    @3
    @4
    @0
    @3
    wa
    #
    cE
    cG
    cedg
    cfv
    #
    cfn
    fusgrmaxsize.e
    @5
    cG
    cfusgr
    wcel
    @6
    cfn
    wcel
    cG
    cV
    fusgrmaxsize.v
    isfusgr
    cG
    fusgrfis
    sylbir
    syl5eqel
    ex
    3ad2ant1
    mpd
end
