include "cumgr.mm"
include "wcel.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "cword.mm"
include "konigsbergiedgw.mm"
include "cvv.mm"
include "wb.mm"
include "cop.mm"
include "opex.mm"
include "eqeltri.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "c3.mm"
include "cs7.mm"
include "s7cli.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "konigsbergvtx.mm"
include "eqtr4i.mm"
include "ciedg.mm"
include "konigsbergiedg.mm"
include "wrdumgr.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem konigsbergumgr
  let cE: class E
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume konigsberg.v: |- V = ( 0 ... 3 )
  assume konigsberg.e: |- E = <" { 0 , 1 } { 0 , 2 } { 0 , 3 } { 1 , 2 } { 1 , 2 } { 2 , 3 } { 2 , 3 } ">
  assume konigsberg.g: |- G = <. V , E >.


  assert |- G e. UMGraph

  proof
    cG
    cumgr
    wcel
    #
    cE
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cV
    cpw
    crab
    cword
    wcel
    #
    vx
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsbergiedgw
    cG
    cvv
    wcel
    cE
    cvv
    cword
    #
    wcel
    @0
    @1
    wb
    cG
    cV
    cE
    cop
    cvv
    konigsberg.g
    cV
    cE
    opex
    eqeltri
    cE
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
    @6
    c2
    c3
    cpr
    #
    @7
    cs7
    #
    @2
    konigsberg.e
    @3
    @4
    @5
    @6
    @6
    @7
    @7
    s7cli
    eqeltri
    vx
    cvv
    cE
    cG
    cV
    cvv
    cV
    cc0
    c3
    cfz
    co
    cG
    cvtx
    cfv
    konigsberg.v
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsbergvtx
    eqtr4i
    cE
    @8
    cG
    ciedg
    cfv
    konigsberg.e
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsbergiedg
    eqtr4i
    wrdumgr
    mp2an
    mpbir
end
