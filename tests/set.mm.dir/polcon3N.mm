include "chlt.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "coc.mm"
include "cfv.mm"
include "cpmap.mm"
include "ciin.mm"
include "cin.mm"
include "simp3.mm"
include "iinss1.mm"
include "sslin.mm"
include "3syl.mm"
include "wceq.mm"
include "eqid.mm"
include "polvalN.mm"
include "3adant3.mm"
include "simp1.mm"
include "simp2.mm"
include "sstrd.mm"
include "syl2anc.mm"
include "3sstr4d.mm"

theorem polcon3N
  let cA: class A
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume 2polss.a: |- A = ( Atoms ` K )
  assume 2polss.p: |- ._|_ = ( _|_P ` K )


  assert |- ( ( K e. HL /\ Y C_ A /\ X C_ Y ) -> ( ._|_ ` Y ) C_ ( ._|_ ` X ) )

  proof
    cK
    chlt
    wcel
    #
    cY
    cA
    wss
    #
    cX
    cY
    wss
    #
    w3a
    #
    cA
    vp
    cY
    vp
    cv
    cK
    coc
    cfv
    #
    cfv
    cK
    cpmap
    cfv
    #
    cfv
    #
    ciin
    #
    cin
    #
    cA
    vp
    cX
    @6
    ciin
    #
    cin
    #
    cY
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    @3
    @2
    @7
    @9
    wss
    @8
    @10
    wss
    @0
    @1
    @2
    simp3
    #
    vp
    cX
    cY
    @6
    iinss1
    @7
    @9
    cA
    sslin
    3syl
    @0
    @1
    @11
    @8
    wceq
    @2
    cA
    chlt
    c.pe
    cK
    @5
    @4
    cY
    vp
    @4
    eqid
    #
    2polss.a
    @5
    eqid
    #
    2polss.p
    polvalN
    3adant3
    @3
    @0
    cX
    cA
    wss
    @12
    @10
    wceq
    @0
    @1
    @2
    simp1
    @3
    cX
    cY
    cA
    @13
    @0
    @1
    @2
    simp2
    sstrd
    cA
    chlt
    c.pe
    cK
    @5
    @4
    cX
    vp
    @14
    2polss.a
    @15
    2polss.p
    polvalN
    syl2anc
    3sstr4d
end
