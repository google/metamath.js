include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "19.26.mm"
include "equid.mm"
include "a1i.mm"
include "ax-gen.mm"
include "wb.mm"
include "equequ1.mm"
include "equequ2.mm"
include "sylan9bb.mm"
include "sps-o.mm"
include "nfa1-o.mm"
include "imbi2d.mm"
include "albid.mm"
include "imbi12d.mm"
include "adantr.mm"
include "mpbii.mm"
include "exp32.mm"
include "sylbir.mm"
include "ad2antll.mm"
include "axc9.mm"
include "impcom.mm"
include "adantrr.mm"
include "equtrr.mm"
include "alimi.mm"
include "syl6.mm"
include "sylbid.mm"
include "adantll.mm"
include "dral2-o.mm"
include "ad2antrr.mm"
include "mpbid.mm"
include "imp.mm"
include "biimprcd.mm"
include "adantlr.mm"
include "ad2antlr.mm"
include "wex.mm"
include "ax6ev.mm"
include "ax-1.mm"
include "alrimiv.mm"
include "adantl.mm"
include "dveeq2-o.mm"
include "im2anan9.mm"
include "sylibr.mm"
include "syl.mm"
include "exlimdv.mm"
include "mpi.mm"
include "a1d.mm"
include "4cases.mm"

theorem ax12eq
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let vv: setvar v


  assert |- ( -. A. x x = y -> ( x = y -> ( z = w -> A. x ( x = y -> z = w ) ) ) )

  proof
    vx
    vz
    weq
    #
    vx
    wal
    #
    vx
    vw
    weq
    #
    vx
    wal
    #
    vx
    vy
    weq
    #
    vx
    wal
    wn
    #
    @4
    vz
    vw
    weq
    #
    @4
    @6
    wi
    #
    vx
    wal
    #
    wi
    #
    wi
    #
    wi
    #
    @1
    @3
    wa
    @0
    @2
    wa
    #
    vx
    wal
    #
    @11
    @0
    @2
    vx
    19.26
    @13
    @5
    @4
    @9
    @13
    @5
    @4
    wa
    #
    wa
    vx
    vx
    weq
    #
    @4
    @15
    wi
    #
    vx
    wal
    #
    wi
    #
    @9
    @17
    @15
    @16
    vx
    @15
    @4
    vx
    equid
    a1i
    ax-gen
    a1i
    @13
    @18
    @9
    wb
    @14
    @13
    @15
    @6
    @17
    @8
    @12
    @15
    @6
    wb
    vx
    @0
    @15
    vz
    vx
    weq
    #
    @2
    @6
    vx
    vz
    vx
    equequ1
    vx
    vw
    vz
    equequ2
    #
    sylan9bb
    sps-o
    #
    @13
    @16
    @7
    vx
    @12
    vx
    nfa1-o
    @13
    @15
    @6
    @4
    @21
    imbi2d
    albid
    imbi12d
    adantr
    mpbii
    exp32
    sylbir
    @1
    @3
    wn
    #
    wa
    #
    @5
    @4
    @9
    @23
    @14
    wa
    @2
    @4
    @2
    wi
    #
    vx
    wal
    #
    wi
    #
    @9
    @22
    @14
    @26
    @1
    @22
    @14
    wa
    #
    @2
    vy
    vw
    weq
    #
    @25
    @4
    @2
    @28
    wb
    @22
    @5
    vx
    vy
    vw
    equequ1
    ad2antll
    @27
    @28
    @28
    vx
    wal
    #
    @25
    @22
    @5
    @28
    @29
    wi
    #
    @4
    @5
    @22
    @30
    vy
    vw
    vx
    axc9
    impcom
    adantrr
    @28
    @24
    vx
    vy
    vw
    vx
    equtrr
    alimi
    syl6
    sylbid
    adantll
    @1
    @26
    @9
    wb
    @22
    @14
    @1
    @2
    @6
    @25
    @8
    @0
    @2
    @6
    wb
    vx
    vx
    vz
    vw
    equequ1
    sps-o
    #
    @24
    @7
    vx
    vz
    vx
    @1
    @2
    @6
    @4
    @31
    imbi2d
    dral2-o
    imbi12d
    ad2antrr
    mpbid
    exp32
    @1
    wn
    #
    @3
    wa
    #
    @5
    @4
    @9
    @33
    @14
    wa
    @19
    @4
    @19
    wi
    #
    vx
    wal
    #
    wi
    #
    @9
    @32
    @14
    @36
    @3
    @32
    @14
    wa
    #
    @19
    vz
    vy
    weq
    #
    @35
    @4
    @19
    @38
    wb
    @32
    @5
    vx
    vy
    vz
    equequ2
    #
    ad2antll
    @37
    @38
    @38
    vx
    wal
    #
    @35
    @32
    @5
    @38
    @40
    wi
    #
    @4
    @32
    @5
    @41
    vz
    vy
    vx
    axc9
    imp
    adantrr
    @38
    @34
    vx
    @4
    @19
    @38
    @39
    biimprcd
    alimi
    syl6
    sylbid
    adantlr
    @3
    @36
    @9
    wb
    @32
    @14
    @3
    @19
    @6
    @35
    @8
    @2
    @19
    @6
    wb
    vx
    @20
    sps-o
    #
    @34
    @7
    vx
    vw
    vx
    @3
    @19
    @6
    @4
    @42
    imbi2d
    dral2-o
    imbi12d
    ad2antlr
    mpbid
    exp32
    @32
    @22
    wa
    #
    @10
    @5
    @43
    @9
    @4
    @43
    vu
    vw
    weq
    #
    vu
    wex
    @9
    vu
    vw
    ax6ev
    @43
    @44
    @9
    vu
    @43
    vv
    vz
    weq
    #
    vv
    wex
    @44
    @9
    wi
    #
    vv
    vz
    ax6ev
    @43
    @45
    @46
    vv
    @43
    @45
    @44
    @9
    @43
    @45
    @44
    wa
    #
    wa
    #
    vv
    vu
    weq
    #
    @4
    @49
    wi
    #
    vx
    wal
    #
    wi
    @9
    @49
    @50
    vx
    @49
    @4
    ax-1
    alrimiv
    @48
    @49
    @6
    @51
    @8
    @47
    @49
    @6
    wb
    #
    @43
    @45
    @49
    vz
    vu
    weq
    @44
    @6
    vv
    vz
    vu
    equequ1
    vu
    vw
    vz
    equequ2
    sylan9bb
    #
    adantl
    @48
    @47
    vx
    wal
    #
    @51
    @8
    wb
    @48
    @45
    vx
    wal
    #
    @44
    vx
    wal
    #
    wa
    #
    @54
    @43
    @47
    @57
    @32
    @45
    @55
    @22
    @44
    @56
    vx
    vz
    vv
    dveeq2-o
    vx
    vw
    vu
    dveeq2-o
    im2anan9
    imp
    @45
    @44
    vx
    19.26
    sylibr
    @54
    @50
    @7
    vx
    @47
    vx
    nfa1-o
    @54
    @49
    @6
    @4
    @47
    @52
    vx
    @53
    sps-o
    imbi2d
    albid
    syl
    imbi12d
    mpbii
    exp32
    exlimdv
    mpi
    exlimdv
    mpi
    a1d
    a1d
    4cases
end
