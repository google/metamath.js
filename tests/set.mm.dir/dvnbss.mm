include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "cpm.mm"
include "co.mm"
include "cn0.mm"
include "w3a.mm"
include "cdvn.mm"
include "cfv.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "wa.mm"
include "dvnff.mm"
include "ffvelrnda.mm"
include "3impa.mm"
include "cvv.mm"
include "wb.mm"
include "cnex.mm"
include "simp1.mm"
include "simp2.mm"
include "elpm2g.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simprd.mm"
include "ssexd.mm"

theorem dvnbss
  let cS: class S
  let cF: class F
  let cN: class N
  let vf: setvar f
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let vm: setvar m
  let cM: class M
  let vs: setvar s


  assert |- ( ( S e. { RR , CC } /\ F e. ( CC ^pm S ) /\ N e. NN0 ) -> dom ( ( S Dn F ) ` N ) C_ dom F )

  proof
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cN
    cS
    cF
    cdvn
    co
    #
    cfv
    #
    cdm
    #
    cc
    @6
    wf
    #
    @7
    cF
    cdm
    #
    wss
    #
    @4
    @6
    cc
    @9
    cpm
    co
    #
    wcel
    #
    @8
    @10
    wa
    #
    @1
    @2
    @3
    @12
    @1
    @2
    wa
    cn0
    @11
    cN
    @5
    cS
    cF
    dvnff
    ffvelrnda
    3impa
    @4
    cc
    cvv
    wcel
    #
    @9
    cvv
    wcel
    @12
    @13
    wb
    cnex
    @4
    @9
    cS
    @0
    @1
    @2
    @3
    simp1
    #
    @4
    @9
    cc
    cF
    wf
    #
    @9
    cS
    wss
    #
    @4
    @2
    @16
    @17
    wa
    #
    @1
    @2
    @3
    simp2
    @4
    @14
    @1
    @2
    @18
    wb
    cnex
    @15
    cc
    cS
    cF
    cvv
    @0
    elpm2g
    sylancr
    mpbid
    simprd
    ssexd
    cc
    @9
    @6
    cvv
    cvv
    elpm2g
    sylancr
    mpbid
    simprd
end
