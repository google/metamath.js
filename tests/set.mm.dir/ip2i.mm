include "c2.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "cmul.mm"
include "cc0.mm"
include "cnv.mm"
include "wcel.mm"
include "cc.mm"
include "phnvi.mm"
include "nvgcl.mm"
include "mp3an.mm"
include "dipcl.mm"
include "addid1i.mm"
include "cn0v.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "nvrinv.mm"
include "mp2an.mm"
include "oveq1i.mm"
include "dip0l.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "df-2.mm"
include "w3a.mm"
include "ax-1cn.mm"
include "3pm3.2i.mm"
include "nvdir.mm"
include "nvsid.mm"
include "oveq12i.mm"
include "3eqtr4ri.mm"
include "ip1i.mm"

theorem ip2i
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume ip1i.1: |- X = ( BaseSet ` U )
  assume ip1i.2: |- G = ( +v ` U )
  assume ip1i.4: |- S = ( .sOLD ` U )
  assume ip1i.7: |- P = ( .iOLD ` U )
  assume ip1i.9: |- U e. CPreHilOLD
  assume ip2i.8: |- A e. X
  assume ip2i.9: |- B e. X


  assert |- ( ( 2 S A ) P B ) = ( 2 x. ( A P B ) )

  proof
    c2
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    cA
    cA
    cG
    co
    #
    cB
    cP
    co
    #
    cA
    c1
    cneg
    cA
    cS
    co
    cG
    co
    #
    cB
    cP
    co
    #
    caddc
    co
    #
    c2
    cA
    cB
    cP
    co
    cmul
    co
    @3
    cc0
    caddc
    co
    @3
    @6
    @1
    @3
    cU
    cnv
    wcel
    #
    @2
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    @3
    cc
    wcel
    cU
    ip1i.9
    phnvi
    #
    @7
    cA
    cX
    wcel
    #
    @11
    @8
    @10
    ip2i.8
    ip2i.8
    cA
    cA
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    nvgcl
    mp3an
    ip2i.9
    @2
    cB
    cP
    cU
    cX
    ip1i.1
    ip1i.7
    dipcl
    mp3an
    addid1i
    @5
    cc0
    @3
    caddc
    @5
    cU
    cn0v
    cfv
    #
    cB
    cP
    co
    #
    cc0
    @4
    @12
    cB
    cP
    @7
    @11
    @4
    @12
    wceq
    @10
    ip2i.8
    cA
    cS
    cU
    cG
    cX
    @12
    ip1i.1
    ip1i.2
    ip1i.4
    @12
    eqid
    #
    nvrinv
    mp2an
    oveq1i
    @7
    @9
    @13
    cc0
    wceq
    @10
    ip2i.9
    cB
    cP
    cU
    cX
    @12
    ip1i.1
    @14
    ip1i.7
    dip0l
    mp2an
    eqtri
    oveq2i
    @0
    @2
    cB
    cP
    @0
    c1
    c1
    caddc
    co
    #
    cA
    cS
    co
    #
    @2
    c2
    @15
    cA
    cS
    df-2
    oveq1i
    @16
    c1
    cA
    cS
    co
    #
    @17
    cG
    co
    #
    @2
    @7
    c1
    cc
    wcel
    #
    @19
    @11
    w3a
    @16
    @18
    wceq
    @10
    @19
    @19
    @11
    ax-1cn
    ax-1cn
    ip2i.8
    3pm3.2i
    c1
    c1
    cA
    cS
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    nvdir
    mp2an
    @17
    cA
    @17
    cA
    cG
    @7
    @11
    @17
    cA
    wceq
    @10
    ip2i.8
    cA
    cS
    cU
    cX
    ip1i.1
    ip1i.4
    nvsid
    mp2an
    #
    @20
    oveq12i
    eqtri
    eqtri
    oveq1i
    3eqtr4ri
    cA
    cA
    cB
    cP
    cS
    cU
    cG
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ip2i.8
    ip2i.8
    ip2i.9
    ip1i
    eqtri
end
