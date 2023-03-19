include "ciedg.mm"
include "cfv.mm"
include "wfun.mm"
include "cclwlks.mm"
include "wbr.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "csn.mm"
include "cedg.mm"
include "wcel.mm"
include "wa.mm"
include "cwlks.mm"
include "wi.mm"
include "isclwlk.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "w3a.mm"
include "simp2r.mm"
include "simp3.mm"
include "simp2l.mm"
include "simpr.mm"
include "anim2i.mm"
include "3adant3.mm"
include "wlkl1loop.mm"
include "syl21anc.mm"
include "jca.mm"
include "3exp.mm"
include "sylbid.mm"
include "com13.mm"
include "syl5bi.mm"
include "3imp.mm"

theorem clwlkl1loop
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( ( Fun ( iEdg ` G ) /\ F ( ClWalks ` G ) P /\ ( # ` F ) = 1 ) -> ( ( P ` 0 ) = ( P ` 1 ) /\ { ( P ` 0 ) } e. ( Edg ` G ) ) )

  proof
    cG
    ciedg
    cfv
    wfun
    #
    cF
    cP
    cG
    cclwlks
    cfv
    wbr
    #
    cF
    chash
    cfv
    #
    c1
    wceq
    #
    cc0
    cP
    cfv
    #
    c1
    cP
    cfv
    #
    wceq
    #
    @4
    csn
    cG
    cedg
    cfv
    wcel
    #
    wa
    #
    @1
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    @4
    @2
    cP
    cfv
    #
    wceq
    #
    wa
    #
    @0
    @3
    @8
    wi
    cP
    cF
    cG
    isclwlk
    @3
    @12
    @0
    @8
    @3
    @12
    @9
    @6
    wa
    #
    @0
    @8
    wi
    @3
    @11
    @6
    @9
    @3
    @10
    @5
    @4
    @2
    c1
    cP
    fveq2
    eqeq2d
    anbi2d
    @3
    @13
    @0
    @8
    @3
    @13
    @0
    w3a
    #
    @6
    @7
    @3
    @9
    @6
    @0
    simp2r
    @14
    @0
    @9
    @3
    @6
    wa
    #
    @7
    @3
    @13
    @0
    simp3
    @3
    @9
    @6
    @0
    simp2l
    @3
    @13
    @15
    @0
    @13
    @6
    @3
    @9
    @6
    simpr
    anim2i
    3adant3
    cP
    cF
    cG
    wlkl1loop
    syl21anc
    jca
    3exp
    sylbid
    com13
    syl5bi
    3imp
end
