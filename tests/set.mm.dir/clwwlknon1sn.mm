include "wcel.mm"
include "c1.mm"
include "co.mm"
include "cs1.mm"
include "csn.mm"
include "wceq.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "wa.mm"
include "c0.mm"
include "clwwlknon1nloop.mm"
include "adantl.mm"
include "cvv.mm"
include "cword.mm"
include "s1cli.mm"
include "elexi.mm"
include "snnz.mm"
include "nesymi.mm"
include "eqeq1.mm"
include "mtbiri.mm"
include "syl.mm"
include "ex.mm"
include "syl5bir.mm"
include "con4d.mm"
include "clwwlknon1loop.mm"
include "impbid.mm"

theorem clwwlknon1sn
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let vw: setvar w
  assume clwwlknon1.v: |- V = ( Vtx ` G )
  assume clwwlknon1.c: |- C = ( ClWWalksNOn ` G )
  assume clwwlknon1.e: |- E = ( Edg ` G )


  assert |- ( X e. V -> ( ( X C 1 ) = { <" X "> } <-> { X } e. E ) )

  proof
    cX
    cV
    wcel
    #
    cX
    c1
    cC
    co
    #
    cX
    cs1
    #
    csn
    #
    wceq
    #
    cX
    csn
    #
    cE
    wcel
    #
    @0
    @6
    @4
    @6
    wn
    @5
    cE
    wnel
    #
    @0
    @4
    wn
    #
    @5
    cE
    df-nel
    @0
    @7
    @8
    @0
    @7
    wa
    @1
    c0
    wceq
    #
    @8
    @7
    @9
    @0
    cC
    cE
    cG
    cV
    cX
    clwwlknon1.v
    clwwlknon1.c
    clwwlknon1.e
    clwwlknon1nloop
    adantl
    @9
    @4
    c0
    @3
    wceq
    @3
    c0
    @2
    @2
    cvv
    cword
    cX
    s1cli
    elexi
    snnz
    nesymi
    @1
    c0
    @3
    eqeq1
    mtbiri
    syl
    ex
    syl5bir
    con4d
    @0
    @6
    @4
    cC
    cE
    cG
    cV
    cX
    clwwlknon1.v
    clwwlknon1.c
    clwwlknon1.e
    clwwlknon1loop
    ex
    impbid
end
