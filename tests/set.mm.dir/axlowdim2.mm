include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cc0.mm"
include "cop.mm"
include "cpr.mm"
include "c3.mm"
include "cfz.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "cee.mm"
include "cv.mm"
include "cbtwn.mm"
include "wbr.mm"
include "w3o.mm"
include "wn.mm"
include "wrex.mm"
include "0re.mm"
include "axlowdimlem5.mm"
include "1re.mm"
include "eqid.mm"
include "axlowdimlem6.mm"
include "wceq.mm"
include "opeq2.mm"
include "breq2d.mm"
include "opeq1.mm"
include "breq1.mm"
include "3orbi123d.mm"
include "notbid.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexbidv.mm"
include "rspc2ev.mm"
include "syl3anc.mm"

theorem axlowdim2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cN: class N

  disjoint N x
  disjoint N y
  disjoint N z
  disjoint x y
  disjoint x z
  disjoint y z
  assert |- ( N e. ( ZZ>= ` 2 ) -> E. x e. ( EE ` N ) E. y e. ( EE ` N ) E. z e. ( EE ` N ) -. ( x Btwn <. y , z >. \/ y Btwn <. z , x >. \/ z Btwn <. x , y >. ) )

  proof
    cN
    c2
    cuz
    cfv
    wcel
    #
    c1
    cc0
    cop
    #
    c2
    cc0
    cop
    #
    cpr
    c3
    cN
    cfz
    co
    cc0
    csn
    cxp
    #
    cun
    #
    cN
    cee
    cfv
    #
    wcel
    c1
    c1
    cop
    @2
    cpr
    @3
    cun
    #
    @5
    wcel
    @4
    @6
    vz
    cv
    #
    cop
    #
    cbtwn
    wbr
    #
    @6
    @7
    @4
    cop
    #
    cbtwn
    wbr
    #
    @7
    @4
    @6
    cop
    #
    cbtwn
    wbr
    #
    w3o
    #
    wn
    #
    vz
    @5
    wrex
    #
    vx
    cv
    #
    vy
    cv
    #
    @7
    cop
    #
    cbtwn
    wbr
    #
    @18
    @7
    @17
    cop
    #
    cbtwn
    wbr
    #
    @7
    @17
    @18
    cop
    #
    cbtwn
    wbr
    #
    w3o
    #
    wn
    #
    vz
    @5
    wrex
    #
    vy
    @5
    wrex
    vx
    @5
    wrex
    cc0
    cc0
    cN
    0re
    0re
    axlowdimlem5
    c1
    cc0
    cN
    1re
    0re
    axlowdimlem5
    @0
    @1
    c2
    c1
    cop
    cpr
    @3
    cun
    #
    @5
    wcel
    @4
    @6
    @28
    cop
    #
    cbtwn
    wbr
    #
    @6
    @28
    @4
    cop
    #
    cbtwn
    wbr
    #
    @28
    @12
    cbtwn
    wbr
    #
    w3o
    #
    wn
    #
    @16
    cc0
    c1
    cN
    0re
    1re
    axlowdimlem5
    @4
    @6
    @28
    cN
    @4
    eqid
    @6
    eqid
    @28
    eqid
    axlowdimlem6
    @15
    @35
    vz
    @28
    @5
    @7
    @28
    wceq
    #
    @14
    @34
    @36
    @9
    @30
    @11
    @32
    @13
    @33
    @36
    @8
    @29
    @4
    cbtwn
    @7
    @28
    @6
    opeq2
    breq2d
    @36
    @10
    @31
    @6
    cbtwn
    @7
    @28
    @4
    opeq1
    breq2d
    @7
    @28
    @12
    cbtwn
    breq1
    3orbi123d
    notbid
    rspcev
    syl2anc
    @27
    @16
    @4
    @19
    cbtwn
    wbr
    #
    @18
    @10
    cbtwn
    wbr
    #
    @7
    @4
    @18
    cop
    #
    cbtwn
    wbr
    #
    w3o
    #
    wn
    #
    vz
    @5
    wrex
    vx
    vy
    @4
    @6
    @5
    @5
    @17
    @4
    wceq
    #
    @26
    @42
    vz
    @5
    @43
    @25
    @41
    @43
    @20
    @37
    @22
    @38
    @24
    @40
    @17
    @4
    @19
    cbtwn
    breq1
    @43
    @21
    @10
    @18
    cbtwn
    @17
    @4
    @7
    opeq2
    breq2d
    @43
    @23
    @39
    @7
    cbtwn
    @17
    @4
    @18
    opeq1
    breq2d
    3orbi123d
    notbid
    rexbidv
    @18
    @6
    wceq
    #
    @42
    @15
    vz
    @5
    @44
    @41
    @14
    @44
    @37
    @9
    @38
    @11
    @40
    @13
    @44
    @19
    @8
    @4
    cbtwn
    @18
    @6
    @7
    opeq1
    breq2d
    @18
    @6
    @10
    cbtwn
    breq1
    @44
    @39
    @12
    @7
    cbtwn
    @18
    @6
    @4
    opeq2
    breq2d
    3orbi123d
    notbid
    rexbidv
    rspc2ev
    syl3anc
end
