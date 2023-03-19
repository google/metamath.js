include "cupgr.mm"
include "wcel.mm"
include "w3a.mm"
include "cs3.mm"
include "c2.mm"
include "cwwlksnon.mm"
include "co.mm"
include "cwwlksn.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cwlks.mm"
include "wbr.mm"
include "chash.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "wwlknon.mm"
include "a1i.mm"
include "s3fv0.mm"
include "s3fv2.mm"
include "anim12i.mm"
include "3adant1.mm"
include "biantrud.mm"
include "3anass.mm"
include "syl6rbbr.mm"
include "wlklnwwlknupgr.mm"
include "bicomd.mm"
include "3ad2ant1.mm"
include "3bitrd.mm"

theorem s3wwlks2on
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let cG: class G
  let cV: class V
  assume s3wwlks2on.v: |- V = ( Vtx ` G )

  disjoint A f
  disjoint B f
  disjoint C f
  disjoint G f
  assert |- ( ( G e. UPGraph /\ A e. V /\ C e. V ) -> ( <" A B C "> e. ( A ( 2 WWalksNOn G ) C ) <-> E. f ( f ( Walks ` G ) <" A B C "> /\ ( # ` f ) = 2 ) ) )

  proof
    cG
    cupgr
    wcel
    #
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cs3
    #
    cA
    cC
    c2
    cG
    cwwlksnon
    co
    co
    wcel
    #
    @4
    c2
    cG
    cwwlksn
    co
    wcel
    #
    cc0
    @4
    cfv
    cA
    wceq
    #
    c2
    @4
    cfv
    cC
    wceq
    #
    w3a
    #
    @6
    vf
    cv
    #
    @4
    cG
    cwlks
    cfv
    wbr
    @10
    chash
    cfv
    c2
    wceq
    wa
    vf
    wex
    #
    @5
    @9
    wb
    @3
    cA
    cC
    cG
    c2
    @4
    wwlknon
    a1i
    @3
    @6
    @6
    @7
    @8
    wa
    #
    wa
    @9
    @3
    @12
    @6
    @1
    @2
    @12
    @0
    @1
    @7
    @2
    @8
    cA
    cB
    cC
    cV
    s3fv0
    cA
    cB
    cC
    cV
    s3fv2
    anim12i
    3adant1
    biantrud
    @6
    @7
    @8
    3anass
    syl6rbbr
    @0
    @1
    @6
    @11
    wb
    @2
    @0
    @11
    @6
    @4
    vf
    cG
    c2
    wlklnwwlknupgr
    bicomd
    3ad2ant1
    3bitrd
end
