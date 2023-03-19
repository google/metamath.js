include "csn.mm"
include "cort.mm"
include "cfv.mm"
include "wcel.mm"
include "csp.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "csm.mm"
include "cmin.mm"
include "cc0.mm"
include "cmv.mm"
include "chil.mm"
include "hicli.mm"
include "hvmulcli.mm"
include "his2sub.mm"
include "mp3an.mm"
include "cc.mm"
include "ax-his3.mm"
include "mulcomi.mm"
include "eqtri.mm"
include "oveq12i.mm"
include "eqtr2i.mm"
include "3eqtr4i.mm"
include "subeq0i.mm"
include "mpbir.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "h1dei.mm"
include "mpbiran.mm"
include "hvsubcli.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "sylbi.mm"
include "wb.mm"
include "orthcom.mm"
include "mp2an.mm"
include "3imtr4g.mm"
include "mpi.mm"
include "syl5eq.mm"
include "mulcli.mm"
include "sylib.mm"
include "eqcomd.mm"
include "bcseqi.mm"

theorem h1de2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume h1de2.1: |- A e. ~H
  assume h1de2.2: |- B e. ~H


  assert |- ( A e. ( _|_ ` ( _|_ ` { B } ) ) -> ( ( B .ih B ) .h A ) = ( ( A .ih B ) .h B ) )

  proof
    cA
    cB
    csn
    cort
    cfv
    cort
    cfv
    wcel
    #
    cA
    cB
    csp
    co
    #
    cB
    cA
    csp
    co
    #
    cmul
    co
    #
    cA
    cA
    csp
    co
    #
    cB
    cB
    csp
    co
    #
    cmul
    co
    #
    wceq
    @5
    cA
    csm
    co
    #
    @1
    cB
    csm
    co
    #
    wceq
    @0
    @6
    @3
    @0
    @6
    @3
    cmin
    co
    #
    cc0
    wceq
    @6
    @3
    wceq
    @0
    @9
    @7
    @8
    cmv
    co
    #
    cA
    csp
    co
    #
    cc0
    @11
    @7
    cA
    csp
    co
    #
    @8
    cA
    csp
    co
    #
    cmin
    co
    #
    @9
    @7
    chil
    wcel
    #
    @8
    chil
    wcel
    #
    cA
    chil
    wcel
    #
    @11
    @14
    wceq
    @5
    cA
    cB
    cB
    h1de2.2
    h1de2.2
    hicli
    #
    h1de2.1
    hvmulcli
    #
    @1
    cB
    cA
    cB
    h1de2.1
    h1de2.2
    hicli
    #
    h1de2.2
    hvmulcli
    #
    h1de2.1
    @7
    @8
    cA
    his2sub
    mp3an
    @12
    @6
    @13
    @3
    cmin
    @12
    @5
    @4
    cmul
    co
    #
    @6
    @5
    cc
    wcel
    #
    @17
    @17
    @12
    @22
    wceq
    @18
    h1de2.1
    h1de2.1
    @5
    cA
    cA
    ax-his3
    mp3an
    @5
    @4
    @18
    cA
    cA
    h1de2.1
    h1de2.1
    hicli
    #
    mulcomi
    eqtri
    @1
    cc
    wcel
    #
    cB
    chil
    wcel
    #
    @17
    @13
    @3
    wceq
    @20
    h1de2.2
    h1de2.1
    @1
    cB
    cA
    ax-his3
    mp3an
    oveq12i
    eqtr2i
    @0
    @10
    cB
    csp
    co
    #
    cc0
    wceq
    #
    @11
    cc0
    wceq
    #
    @27
    @7
    cB
    csp
    co
    #
    @8
    cB
    csp
    co
    #
    cmin
    co
    #
    cc0
    @15
    @16
    @26
    @27
    @32
    wceq
    @19
    @21
    h1de2.2
    @7
    @8
    cB
    his2sub
    mp3an
    @32
    cc0
    wceq
    @30
    @31
    wceq
    @5
    @1
    cmul
    co
    #
    @1
    @5
    cmul
    co
    #
    @30
    @31
    @5
    @1
    @18
    @20
    mulcomi
    @23
    @17
    @26
    @30
    @33
    wceq
    @18
    h1de2.1
    h1de2.2
    @5
    cA
    cB
    ax-his3
    mp3an
    @25
    @26
    @26
    @31
    @34
    wceq
    @20
    h1de2.2
    h1de2.2
    @1
    cB
    cB
    ax-his3
    mp3an
    3eqtr4i
    @30
    @31
    @7
    cB
    @19
    h1de2.2
    hicli
    @8
    cB
    @21
    h1de2.2
    hicli
    subeq0i
    mpbir
    eqtri
    @0
    cB
    @10
    csp
    co
    #
    cc0
    wceq
    #
    cA
    @10
    csp
    co
    #
    cc0
    wceq
    #
    @28
    @29
    @0
    cB
    vx
    cv
    #
    csp
    co
    #
    cc0
    wceq
    #
    cA
    @39
    csp
    co
    #
    cc0
    wceq
    #
    wi
    #
    vx
    chil
    wral
    #
    @36
    @38
    wi
    #
    @0
    @17
    @45
    h1de2.1
    vx
    cA
    cB
    h1de2.2
    h1dei
    mpbiran
    @10
    chil
    wcel
    #
    @45
    @46
    wi
    @7
    @8
    @19
    @21
    hvsubcli
    #
    @44
    @46
    vx
    @10
    chil
    @39
    @10
    wceq
    #
    @41
    @36
    @43
    @38
    @49
    @40
    @35
    cc0
    @39
    @10
    cB
    csp
    oveq2
    eqeq1d
    @49
    @42
    @37
    cc0
    @39
    @10
    cA
    csp
    oveq2
    eqeq1d
    imbi12d
    rspcv
    ax-mp
    sylbi
    @47
    @26
    @28
    @36
    wb
    @48
    h1de2.2
    @10
    cB
    orthcom
    mp2an
    @47
    @17
    @29
    @38
    wb
    @48
    h1de2.1
    @10
    cA
    orthcom
    mp2an
    3imtr4g
    mpi
    syl5eq
    @6
    @3
    @4
    @5
    @24
    @18
    mulcli
    @1
    @2
    @20
    cB
    cA
    h1de2.2
    h1de2.1
    hicli
    mulcli
    subeq0i
    sylib
    eqcomd
    cA
    cB
    h1de2.1
    h1de2.2
    bcseqi
    sylib
end
