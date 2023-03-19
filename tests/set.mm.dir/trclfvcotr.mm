include "wcel.mm"
include "cv.mm"
include "ctcl.mm"
include "cfv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "ccom.mm"
include "wss.mm"
include "cotr.mm"
include "sp.mm"
include "19.21bbi.mm"
include "sylbi.mm"
include "adantl.mm"
include "a2i.mm"
include "alimi.mm"
include "ax-gen.mm"
include "brtrclfv.mm"
include "anbi12d.mm"
include "jcab.mm"
include "albii.mm"
include "19.26.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "imbi12d.mm"
include "albidv.mm"
include "2albidv.mm"
include "mpbiri.mm"
include "sylibr.mm"

theorem trclfvcotr
  let cR: class R
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vr: setvar r


  assert |- ( R e. V -> ( ( t+ ` R ) o. ( t+ ` R ) ) C_ ( t+ ` R ) )

  proof
    cR
    cV
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    cR
    ctcl
    cfv
    #
    wbr
    #
    @2
    vc
    cv
    #
    @3
    wbr
    #
    wa
    #
    @1
    @5
    @3
    wbr
    #
    wi
    #
    vc
    wal
    #
    vb
    wal
    va
    wal
    #
    @3
    @3
    ccom
    @3
    wss
    @0
    @11
    cR
    vr
    cv
    #
    wss
    #
    @12
    @12
    ccom
    @12
    wss
    #
    wa
    #
    @1
    @2
    @12
    wbr
    #
    @2
    @5
    @12
    wbr
    #
    wa
    #
    wi
    #
    vr
    wal
    #
    @15
    @1
    @5
    @12
    wbr
    #
    wi
    #
    vr
    wal
    #
    wi
    #
    vc
    wal
    #
    vb
    wal
    #
    va
    wal
    @26
    va
    @25
    vb
    @24
    vc
    @19
    @22
    vr
    @15
    @18
    @21
    @14
    @18
    @21
    wi
    #
    @13
    @14
    @27
    vc
    wal
    vb
    wal
    #
    va
    wal
    #
    @27
    va
    vb
    vc
    @12
    cotr
    @29
    @27
    vb
    vc
    @28
    va
    sp
    19.21bbi
    sylbi
    adantl
    a2i
    alimi
    ax-gen
    ax-gen
    ax-gen
    @0
    @10
    @25
    va
    vb
    @0
    @9
    @24
    vc
    @0
    @7
    @20
    @8
    @23
    @0
    @7
    @15
    @16
    wi
    #
    vr
    wal
    #
    @15
    @17
    wi
    #
    vr
    wal
    #
    wa
    #
    @20
    @0
    @4
    @31
    @6
    @33
    @1
    @2
    cR
    cV
    vr
    brtrclfv
    @2
    @5
    cR
    cV
    vr
    brtrclfv
    anbi12d
    @20
    @30
    @32
    wa
    #
    vr
    wal
    @34
    @19
    @35
    vr
    @15
    @16
    @17
    jcab
    albii
    @30
    @32
    vr
    19.26
    bitri
    syl6bbr
    @1
    @5
    cR
    cV
    vr
    brtrclfv
    imbi12d
    albidv
    2albidv
    mpbiri
    va
    vb
    vc
    @3
    cotr
    sylibr
end
