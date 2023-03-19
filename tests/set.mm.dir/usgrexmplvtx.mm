include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "ciedg.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "c2.mm"
include "ctp.mm"
include "c3.mm"
include "c4.mm"
include "cpr.mm"
include "cun.mm"
include "usgrexmpllem.mm"
include "id.mm"
include "cfz.mm"
include "co.mm"
include "fz0to4untppr.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "adantr.mm"
include "ax-mp.mm"

theorem usgrexmplvtx
  let cE: class E
  let cG: class G
  let cV: class V
  assume usgrexmpl.v: |- V = ( 0 ... 4 )
  assume usgrexmpl.e: |- E = <" { 0 , 1 } { 1 , 2 } { 2 , 0 } { 0 , 3 } ">
  assume usgrexmpl.g: |- G = <. V , E >.


  assert |- ( Vtx ` G ) = ( { 0 , 1 , 2 } u. { 3 , 4 } )

  proof
    cG
    cvtx
    cfv
    #
    cV
    wceq
    #
    cG
    ciedg
    cfv
    cE
    wceq
    #
    wa
    @0
    cc0
    c1
    c2
    ctp
    c3
    c4
    cpr
    cun
    #
    wceq
    #
    cE
    cG
    cV
    usgrexmpl.v
    usgrexmpl.e
    usgrexmpl.g
    usgrexmpllem
    @1
    @4
    @2
    @1
    @0
    cV
    @3
    @1
    id
    cV
    cc0
    c4
    cfz
    co
    @3
    usgrexmpl.v
    fz0to4untppr
    eqtri
    syl6eq
    adantr
    ax-mp
end
