include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cdiv.mm"
include "caddc.mm"
include "wceq.mm"
include "cmin.mm"
include "simpll.mm"
include "simprl.mm"
include "reccl.mm"
include "adantr.mm"
include "mul32d.mm"
include "recid.mm"
include "oveq1d.mm"
include "mulid2.mm"
include "ad2antrl.mm"
include "3eqtrd.mm"
include "adantl.mm"
include "mulassd.mm"
include "oveq2d.mm"
include "mulid1.mm"
include "ad2antrr.mm"
include "oveq12d.mm"
include "mulcl.mm"
include "ad2ant2r.mm"
include "adddid.mm"
include "addcom.mm"
include "3eqtr4d.mm"
include "mulid1d.mm"
include "eqeq12d.mm"
include "wb.mm"
include "addcl.mm"
include "syl2an.mm"
include "mulne0.mm"
include "ax-1cn.mm"
include "mulcan.mm"
include "mp3an2.mm"
include "syl12anc.mm"
include "eqcom.mm"
include "muleqadd.mm"
include "syl5bb.mm"
include "3bitr3d.mm"

theorem conjmul
  let cP: class P
  let cQ: class Q


  assert |- ( ( ( P e. CC /\ P =/= 0 ) /\ ( Q e. CC /\ Q =/= 0 ) ) -> ( ( ( 1 / P ) + ( 1 / Q ) ) = 1 <-> ( ( P - 1 ) x. ( Q - 1 ) ) = 1 ) )

  proof
    cP
    cc
    wcel
    #
    cP
    cc0
    wne
    #
    wa
    #
    cQ
    cc
    wcel
    #
    cQ
    cc0
    wne
    #
    wa
    #
    wa
    #
    cP
    cQ
    cmul
    co
    #
    c1
    cP
    cdiv
    co
    #
    c1
    cQ
    cdiv
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    @7
    c1
    cmul
    co
    #
    wceq
    #
    cP
    cQ
    caddc
    co
    #
    @7
    wceq
    #
    @10
    c1
    wceq
    #
    cP
    c1
    cmin
    co
    cQ
    c1
    cmin
    co
    cmul
    co
    c1
    wceq
    #
    @6
    @11
    @14
    @12
    @7
    @6
    @7
    @8
    cmul
    co
    #
    @7
    @9
    cmul
    co
    #
    caddc
    co
    cQ
    cP
    caddc
    co
    #
    @11
    @14
    @6
    @18
    cQ
    @19
    cP
    caddc
    @6
    @18
    cP
    @8
    cmul
    co
    #
    cQ
    cmul
    co
    #
    c1
    cQ
    cmul
    co
    #
    cQ
    @6
    cP
    cQ
    @8
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    #
    @2
    @8
    cc
    wcel
    #
    @5
    cP
    reccl
    #
    adantr
    #
    mul32d
    @2
    @22
    @23
    wceq
    @5
    @2
    @21
    c1
    cQ
    cmul
    cP
    recid
    oveq1d
    adantr
    @3
    @23
    cQ
    wceq
    @2
    @4
    cQ
    mulid2
    ad2antrl
    3eqtrd
    @6
    @19
    cP
    cQ
    @9
    cmul
    co
    #
    cmul
    co
    #
    cP
    c1
    cmul
    co
    #
    cP
    @6
    cP
    cQ
    @9
    @24
    @25
    @5
    @9
    cc
    wcel
    #
    @2
    cQ
    reccl
    #
    adantl
    #
    mulassd
    @5
    @30
    @31
    wceq
    @2
    @5
    @29
    c1
    cP
    cmul
    cQ
    recid
    oveq2d
    adantl
    @0
    @31
    cP
    wceq
    @1
    @5
    cP
    mulid1
    ad2antrr
    3eqtrd
    oveq12d
    @6
    @7
    @8
    @9
    @0
    @3
    @7
    cc
    wcel
    #
    @1
    @4
    cP
    cQ
    mulcl
    #
    ad2ant2r
    #
    @28
    @34
    adddid
    @0
    @3
    @14
    @20
    wceq
    @1
    @4
    cP
    cQ
    addcom
    ad2ant2r
    3eqtr4d
    @0
    @3
    @12
    @7
    wceq
    @1
    @4
    @0
    @3
    wa
    #
    @7
    @36
    mulid1d
    ad2ant2r
    eqeq12d
    @6
    @10
    cc
    wcel
    #
    @35
    @7
    cc0
    wne
    #
    @13
    @16
    wb
    #
    @2
    @26
    @32
    @39
    @5
    @27
    @33
    @8
    @9
    addcl
    syl2an
    @37
    cP
    cQ
    mulne0
    @39
    c1
    cc
    wcel
    @35
    @40
    wa
    @41
    ax-1cn
    @10
    c1
    @7
    mulcan
    mp3an2
    syl12anc
    @0
    @3
    @15
    @17
    wb
    @1
    @4
    @15
    @7
    @14
    wceq
    @38
    @17
    @14
    @7
    eqcom
    cP
    cQ
    muleqadd
    syl5bb
    ad2ant2r
    3bitr3d
end
