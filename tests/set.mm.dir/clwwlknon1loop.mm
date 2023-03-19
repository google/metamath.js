include "wcel.mm"
include "csn.mm"
include "wa.mm"
include "c1.mm"
include "co.mm"
include "cs1.mm"
include "wceq.mm"
include "cv.mm"
include "cword.mm"
include "wb.mm"
include "wal.mm"
include "simprl.mm"
include "s1cl.mm"
include "adantr.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "simpr.mm"
include "anim1i.mm"
include "ancomd.mm"
include "jca.mm"
include "ex.mm"
include "impbid2.mm"
include "alrimiv.mm"
include "crab.mm"
include "clwwlknon1.mm"
include "eqeq1d.mm"
include "rabeqsn.mm"
include "syl6bb.mm"

theorem clwwlknon1loop
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let vw: setvar w
  assume clwwlknon1.v: |- V = ( Vtx ` G )
  assume clwwlknon1.c: |- C = ( ClWWalksNOn ` G )
  assume clwwlknon1.e: |- E = ( Edg ` G )


  assert |- ( ( X e. V /\ { X } e. E ) -> ( X C 1 ) = { <" X "> } )

  proof
    cX
    cV
    wcel
    #
    cX
    csn
    cE
    wcel
    #
    wa
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
    vw
    cv
    #
    cV
    cword
    #
    wcel
    #
    @7
    @4
    wceq
    #
    @1
    wa
    #
    wa
    #
    @10
    wb
    #
    vw
    wal
    #
    @2
    @13
    vw
    @2
    @12
    @10
    @9
    @10
    @1
    simprl
    @2
    @10
    @12
    @2
    @10
    wa
    #
    @9
    @11
    @15
    @9
    @4
    @8
    wcel
    #
    @2
    @16
    @10
    @0
    @16
    @1
    cX
    cV
    s1cl
    adantr
    adantr
    @10
    @9
    @16
    wb
    @2
    @7
    @4
    @8
    eleq1
    adantl
    mpbird
    @15
    @1
    @10
    @2
    @1
    @10
    @0
    @1
    simpr
    anim1i
    ancomd
    jca
    ex
    impbid2
    alrimiv
    @2
    @6
    @11
    vw
    @8
    crab
    #
    @5
    wceq
    #
    @14
    @0
    @6
    @18
    wb
    @1
    @0
    @3
    @17
    @5
    vw
    cC
    cE
    cG
    cV
    cX
    clwwlknon1.v
    clwwlknon1.c
    clwwlknon1.e
    clwwlknon1
    eqeq1d
    adantr
    @11
    vw
    @8
    @4
    rabeqsn
    syl6bb
    mpbird
end
