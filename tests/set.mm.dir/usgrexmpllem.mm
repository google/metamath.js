include "cvtx.mm"
include "cfv.mm"
include "wceq.mm"
include "ciedg.mm"
include "wa.mm"
include "cop.mm"
include "cvv.mm"
include "wcel.mm"
include "cc0.mm"
include "c4.mm"
include "cfz.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "c3.mm"
include "cs4.mm"
include "cword.mm"
include "s4cli.mm"
include "elexi.mm"
include "opvtxfv.mm"
include "opiedgfv.mm"
include "jca.mm"
include "mp2an.mm"
include "fveq2i.mm"
include "eqeq1i.mm"
include "anbi12i.mm"
include "mpbir.mm"

theorem usgrexmpllem
  let cE: class E
  let cG: class G
  let cV: class V
  assume usgrexmpl.v: |- V = ( 0 ... 4 )
  assume usgrexmpl.e: |- E = <" { 0 , 1 } { 1 , 2 } { 2 , 0 } { 0 , 3 } ">
  assume usgrexmpl.g: |- G = <. V , E >.


  assert |- ( ( Vtx ` G ) = V /\ ( iEdg ` G ) = E )

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
    #
    cE
    wceq
    #
    wa
    cV
    cE
    cop
    #
    cvtx
    cfv
    #
    cV
    wceq
    #
    @4
    ciedg
    cfv
    #
    cE
    wceq
    #
    wa
    #
    cV
    cvv
    wcel
    #
    cE
    cvv
    wcel
    #
    @9
    cV
    cc0
    c4
    cfz
    co
    cvv
    usgrexmpl.v
    cc0
    c4
    cfz
    ovex
    eqeltri
    cE
    cc0
    c1
    cpr
    #
    c1
    c2
    cpr
    #
    c2
    cc0
    cpr
    #
    cc0
    c3
    cpr
    #
    cs4
    #
    cvv
    usgrexmpl.e
    @16
    cvv
    cword
    @12
    @13
    @14
    @15
    s4cli
    elexi
    eqeltri
    @10
    @11
    wa
    @6
    @8
    cE
    cV
    cvv
    cvv
    opvtxfv
    cE
    cV
    cvv
    cvv
    opiedgfv
    jca
    mp2an
    @1
    @6
    @3
    @8
    @0
    @5
    cV
    cG
    @4
    cvtx
    usgrexmpl.g
    fveq2i
    eqeq1i
    @2
    @7
    cE
    cG
    @4
    ciedg
    usgrexmpl.g
    fveq2i
    eqeq1i
    anbi12i
    mpbir
end
