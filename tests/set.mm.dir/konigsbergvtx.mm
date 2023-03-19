include "cvtx.mm"
include "cfv.mm"
include "cc0.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "cs7.mm"
include "cop.mm"
include "opeq12i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "cvv.mm"
include "wcel.mm"
include "cword.mm"
include "wceq.mm"
include "ovex.mm"
include "s7cli.mm"
include "opvtxfv.mm"
include "mp2an.mm"

theorem konigsbergvtx
  let cE: class E
  let cG: class G
  let cV: class V
  assume konigsberg.v: |- V = ( 0 ... 3 )
  assume konigsberg.e: |- E = <" { 0 , 1 } { 0 , 2 } { 0 , 3 } { 1 , 2 } { 1 , 2 } { 2 , 3 } { 2 , 3 } ">
  assume konigsberg.g: |- G = <. V , E >.


  assert |- ( Vtx ` G ) = ( 0 ... 3 )

  proof
    cG
    cvtx
    cfv
    cc0
    c3
    cfz
    co
    #
    cc0
    c1
    cpr
    #
    cc0
    c2
    cpr
    #
    cc0
    c3
    cpr
    #
    c1
    c2
    cpr
    #
    @4
    c2
    c3
    cpr
    #
    @5
    cs7
    #
    cop
    #
    cvtx
    cfv
    #
    @0
    cG
    @7
    cvtx
    cG
    cV
    cE
    cop
    @7
    konigsberg.g
    cV
    @0
    cE
    @6
    konigsberg.v
    konigsberg.e
    opeq12i
    eqtri
    fveq2i
    @0
    cvv
    wcel
    @6
    cvv
    cword
    #
    wcel
    @8
    @0
    wceq
    cc0
    c3
    cfz
    ovex
    @1
    @2
    @3
    @4
    @4
    @5
    @5
    s7cli
    @6
    @0
    cvv
    @9
    opvtxfv
    mp2an
    eqtri
end
