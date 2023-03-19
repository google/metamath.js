include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "cexp.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wi.mm"
include "wa.mm"
include "eldifsn.mm"
include "difss.mm"
include "cv.mm"
include "cmul.mm"
include "mulcl.mm"
include "ad2ant2r.mm"
include "mulne0.mm"
include "sylanbrc.mm"
include "syl2anb.mm"
include "c1.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "mpbir2an.mm"
include "cdiv.mm"
include "reccl.mm"
include "recne0.mm"
include "jca.mm"
include "3imtr4i.mm"
include "adantr.mm"
include "expcl2lem.mm"
include "3expia.mm"
include "sylanbr.mm"
include "anabss3.mm"
include "3impia.mm"

theorem expclzlem
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ A =/= 0 /\ N e. ZZ ) -> ( A ^ N ) e. ( CC \ { 0 } ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    cN
    cz
    wcel
    #
    cA
    cN
    cexp
    co
    cc
    cc0
    csn
    #
    cdif
    #
    wcel
    #
    @0
    @1
    @2
    @5
    wi
    #
    @0
    @1
    wa
    cA
    @4
    wcel
    #
    @1
    @6
    cA
    cc
    cc0
    eldifsn
    @7
    @1
    @2
    @5
    vx
    vy
    cA
    cN
    @4
    cc
    @3
    difss
    vx
    cv
    #
    @4
    wcel
    #
    @8
    cc
    wcel
    #
    @8
    cc0
    wne
    #
    wa
    #
    vy
    cv
    #
    cc
    wcel
    #
    @13
    cc0
    wne
    #
    wa
    #
    @8
    @13
    cmul
    co
    #
    @4
    wcel
    #
    @13
    @4
    wcel
    @8
    cc
    cc0
    eldifsn
    #
    @13
    cc
    cc0
    eldifsn
    @12
    @16
    wa
    @17
    cc
    wcel
    #
    @17
    cc0
    wne
    @18
    @10
    @14
    @20
    @11
    @15
    @8
    @13
    mulcl
    ad2ant2r
    @8
    @13
    mulne0
    @17
    cc
    cc0
    eldifsn
    sylanbrc
    syl2anb
    c1
    @4
    wcel
    c1
    cc
    wcel
    c1
    cc0
    wne
    ax-1cn
    ax-1ne0
    c1
    cc
    cc0
    eldifsn
    mpbir2an
    @9
    c1
    @8
    cdiv
    co
    #
    @4
    wcel
    #
    @11
    @12
    @21
    cc
    wcel
    #
    @21
    cc0
    wne
    #
    wa
    @9
    @22
    @12
    @23
    @24
    @8
    reccl
    @8
    recne0
    jca
    @19
    @21
    cc
    cc0
    eldifsn
    3imtr4i
    adantr
    expcl2lem
    3expia
    sylanbr
    anabss3
    3impia
end
