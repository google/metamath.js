include "c3.mm"
include "cvtxdg.mm"
include "cfv.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "cpr.mm"
include "cs6.mm"
include "cop.mm"
include "cvtx.mm"
include "ovex.mm"
include "cvv.mm"
include "cword.mm"
include "s6cli.mm"
include "elexi.mm"
include "opvtxfvi.mm"
include "eqcomi.mm"
include "cn0.mm"
include "wcel.mm"
include "3nn0.mm"
include "nn0fz0.mm"
include "mpbi.mm"
include "ciedg.mm"
include "opiedgfvi.mm"
include "cs1.mm"
include "cs7.mm"
include "cconcat.mm"
include "wceq.mm"
include "cv.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "s1cli.mm"
include "df-s7.mm"
include "eqid.mm"
include "konigsbergssiedgw.mm"
include "mp3an.mm"
include "cs5.mm"
include "s5cli.mm"
include "cs2.mm"
include "s2cli.mm"
include "s5s2.mm"
include "cs4.mm"
include "s4cli.mm"
include "cs3.mm"
include "s3cli.mm"
include "s4s3.mm"
include "s3s4.mm"
include "s2s5.mm"
include "s1s6.mm"
include "0ex.mm"
include "wrd0.mm"
include "vtxdg0e.mm"
include "mp2an.mm"
include "0elfz.mm"
include "ax-mp.mm"
include "3ne0.mm"
include "necomi.mm"
include "1nn0.mm"
include "1le3.mm"
include "elfz2nn0.mm"
include "mpbir3an.mm"
include "1re.mm"
include "1lt3.mm"
include "ltneii.mm"
include "s0s1.mm"
include "eqtri.mm"
include "vdegp1ai.mm"
include "2nn0.mm"
include "2re.mm"
include "3re.mm"
include "2lt3.mm"
include "ltleii.mm"
include "df-s2.mm"
include "df-s3.mm"
include "vdegp1ci.mm"
include "0p1e1.mm"
include "df-s4.mm"
include "df-s5.mm"
include "df-s6.mm"
include "1p1e2.mm"
include "konigsbergvtx.mm"
include "konigsbergiedg.mm"
include "2p1e3.mm"

theorem konigsberglem3
  let cE: class E
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume konigsberg.v: |- V = ( 0 ... 3 )
  assume konigsberg.e: |- E = <" { 0 , 1 } { 0 , 2 } { 0 , 3 } { 1 , 2 } { 1 , 2 } { 2 , 3 } { 2 , 3 } ">
  assume konigsberg.g: |- G = <. V , E >.


  assert |- ( ( VtxDeg ` G ) ` 3 ) = 3

  proof
    c3
    cG
    cvtxdg
    cfv
    cfv
    c2
    c1
    caddc
    co
    c3
    vx
    c2
    c3
    cG
    cc0
    c3
    cfz
    co
    #
    cc0
    c1
    cpr
    #
    cc0
    c2
    cpr
    #
    cc0
    c3
    cpr
    #
    c1
    c2
    cpr
    #
    @4
    c2
    c3
    cpr
    #
    cs6
    #
    cop
    #
    @6
    @0
    c2
    @7
    cvtx
    cfv
    @0
    @6
    @0
    cc0
    c3
    cfz
    ovex
    #
    @6
    cvv
    cword
    #
    @1
    @2
    @3
    @4
    @4
    @5
    s6cli
    #
    elexi
    #
    opvtxfvi
    #
    eqcomi
    c3
    cn0
    wcel
    #
    c3
    @0
    wcel
    #
    3nn0
    c3
    nn0fz0
    mpbi
    #
    @7
    ciedg
    cfv
    #
    @6
    @6
    @0
    @8
    @11
    opiedgfvi
    #
    eqcomi
    @6
    @9
    wcel
    @5
    cs1
    #
    @9
    wcel
    @1
    @2
    @3
    @4
    @4
    @5
    @5
    cs7
    #
    @6
    @18
    cconcat
    co
    #
    wceq
    @6
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    vx
    @0
    cpw
    c0
    csn
    cdif
    crab
    #
    cword
    #
    wcel
    @10
    @5
    s1cli
    @1
    @2
    @3
    @4
    @4
    @5
    @5
    df-s7
    #
    vx
    @6
    @18
    @19
    @0
    @19
    cop
    #
    @0
    @0
    eqid
    #
    @19
    eqid
    #
    @24
    eqid
    #
    konigsbergssiedgw
    mp3an
    c3
    @7
    cvtxdg
    cfv
    cfv
    c1
    c1
    caddc
    co
    c2
    vx
    c1
    c3
    @7
    @0
    @1
    @2
    @3
    @4
    @4
    cs5
    #
    cop
    #
    @28
    @0
    c2
    @29
    cvtx
    cfv
    @0
    @28
    @0
    @8
    @28
    @9
    @1
    @2
    @3
    @4
    @4
    s5cli
    #
    elexi
    #
    opvtxfvi
    #
    eqcomi
    @15
    @29
    ciedg
    cfv
    #
    @28
    @28
    @0
    @8
    @31
    opiedgfvi
    #
    eqcomi
    @28
    @9
    wcel
    @5
    @5
    cs2
    #
    @9
    wcel
    @19
    @28
    @35
    cconcat
    co
    wceq
    @28
    @22
    wcel
    @30
    @5
    @5
    s2cli
    @1
    @2
    @3
    @4
    @4
    @5
    @5
    s5s2
    vx
    @28
    @35
    @19
    @24
    @0
    @25
    @26
    @27
    konigsbergssiedgw
    mp3an
    vx
    c1
    c3
    @29
    @0
    @1
    @2
    @3
    @4
    cs4
    #
    cop
    #
    @36
    @0
    c1
    c2
    @37
    cvtx
    cfv
    @0
    @36
    @0
    @8
    @36
    @9
    @1
    @2
    @3
    @4
    s4cli
    #
    elexi
    #
    opvtxfvi
    #
    eqcomi
    @15
    @37
    ciedg
    cfv
    #
    @36
    @36
    @0
    @8
    @39
    opiedgfvi
    #
    eqcomi
    @36
    @9
    wcel
    @4
    @5
    @5
    cs3
    #
    @9
    wcel
    @19
    @36
    @43
    cconcat
    co
    wceq
    @36
    @22
    wcel
    @38
    @4
    @5
    @5
    s3cli
    @1
    @2
    @3
    @4
    @4
    @5
    @5
    s4s3
    vx
    @36
    @43
    @19
    @24
    @0
    @25
    @26
    @27
    konigsbergssiedgw
    mp3an
    vx
    c1
    c3
    @37
    @0
    @1
    @2
    @3
    cs3
    #
    cop
    #
    @44
    @0
    c1
    c2
    @45
    cvtx
    cfv
    @0
    @44
    @0
    @8
    @44
    @9
    @1
    @2
    @3
    s3cli
    #
    elexi
    #
    opvtxfvi
    #
    eqcomi
    @15
    @45
    ciedg
    cfv
    #
    @44
    @44
    @0
    @8
    @47
    opiedgfvi
    #
    eqcomi
    @44
    @9
    wcel
    @4
    @4
    @5
    @5
    cs4
    #
    @9
    wcel
    @19
    @44
    @51
    cconcat
    co
    wceq
    @44
    @22
    wcel
    @46
    @4
    @4
    @5
    @5
    s4cli
    @1
    @2
    @3
    @4
    @4
    @5
    @5
    s3s4
    vx
    @44
    @51
    @19
    @24
    @0
    @25
    @26
    @27
    konigsbergssiedgw
    mp3an
    c3
    @45
    cvtxdg
    cfv
    cfv
    cc0
    c1
    caddc
    co
    c1
    vx
    cc0
    c3
    @45
    @0
    @1
    @2
    cs2
    #
    cop
    #
    @52
    @0
    cc0
    @53
    cvtx
    cfv
    @0
    @52
    @0
    @8
    @52
    @9
    @1
    @2
    s2cli
    #
    elexi
    #
    opvtxfvi
    #
    eqcomi
    @15
    @53
    ciedg
    cfv
    #
    @52
    @52
    @0
    @8
    @55
    opiedgfvi
    #
    eqcomi
    @52
    @9
    wcel
    @3
    @4
    @4
    @5
    @5
    cs5
    #
    @9
    wcel
    @19
    @52
    @59
    cconcat
    co
    wceq
    @52
    @22
    wcel
    @54
    @3
    @4
    @4
    @5
    @5
    s5cli
    @1
    @2
    @3
    @4
    @4
    @5
    @5
    s2s5
    vx
    @52
    @59
    @19
    @24
    @0
    @25
    @26
    @27
    konigsbergssiedgw
    mp3an
    vx
    cc0
    c3
    @53
    @0
    @1
    cs1
    #
    cop
    #
    @60
    @0
    cc0
    c2
    @61
    cvtx
    cfv
    @0
    @60
    @0
    @8
    @60
    @9
    @1
    s1cli
    #
    elexi
    #
    opvtxfvi
    #
    eqcomi
    @15
    @61
    ciedg
    cfv
    #
    @60
    @60
    @0
    @8
    @63
    opiedgfvi
    #
    eqcomi
    @60
    @9
    wcel
    @2
    @3
    @4
    @4
    @5
    @5
    cs6
    #
    @9
    wcel
    @19
    @60
    @67
    cconcat
    co
    wceq
    @60
    @22
    wcel
    @62
    @2
    @3
    @4
    @4
    @5
    @5
    s6cli
    @1
    @2
    @3
    @4
    @4
    @5
    @5
    s1s6
    vx
    @60
    @67
    @19
    @24
    @0
    @25
    @26
    @27
    konigsbergssiedgw
    mp3an
    vx
    cc0
    c3
    @61
    @0
    c0
    cop
    #
    c0
    @0
    cc0
    c1
    @68
    cvtx
    cfv
    @0
    c0
    @0
    @8
    0ex
    opvtxfvi
    eqcomi
    #
    @15
    @68
    ciedg
    cfv
    c0
    c0
    @0
    @8
    0ex
    opiedgfvi
    eqcomi
    #
    @21
    wrd0
    @14
    c0
    c0
    wceq
    c3
    @68
    cvtxdg
    cfv
    cfv
    cc0
    wceq
    @15
    c0
    eqid
    c3
    @68
    c0
    @0
    @69
    @70
    vtxdg0e
    mp2an
    @64
    @13
    cc0
    @0
    wcel
    3nn0
    c3
    0elfz
    ax-mp
    #
    c3
    cc0
    3ne0
    necomi
    #
    c1
    @0
    wcel
    c1
    cn0
    wcel
    @13
    c1
    c3
    cle
    wbr
    1nn0
    3nn0
    1le3
    c1
    c3
    elfz2nn0
    mpbir3an
    #
    c1
    c3
    1re
    1lt3
    ltneii
    #
    @65
    @60
    c0
    @60
    cconcat
    co
    @66
    @1
    s0s1
    eqtri
    vdegp1ai
    @56
    @71
    @72
    c2
    @0
    wcel
    c2
    cn0
    wcel
    @13
    c2
    c3
    cle
    wbr
    2nn0
    3nn0
    c2
    c3
    2re
    3re
    2lt3
    ltleii
    c2
    c3
    elfz2nn0
    mpbir3an
    #
    c2
    c3
    2re
    2lt3
    ltneii
    #
    @57
    @52
    @60
    @2
    cs1
    cconcat
    co
    @58
    @1
    @2
    df-s2
    eqtri
    vdegp1ai
    @48
    @71
    @72
    @49
    @44
    @52
    @3
    cs1
    cconcat
    co
    @50
    @1
    @2
    @3
    df-s3
    eqtri
    vdegp1ci
    0p1e1
    eqtri
    @40
    @73
    @74
    @75
    @76
    @41
    @36
    @44
    @4
    cs1
    #
    cconcat
    co
    @42
    @1
    @2
    @3
    @4
    df-s4
    eqtri
    vdegp1ai
    @32
    @73
    @74
    @75
    @76
    @33
    @28
    @36
    @77
    cconcat
    co
    @34
    @1
    @2
    @3
    @4
    @4
    df-s5
    eqtri
    vdegp1ai
    @12
    @75
    @76
    @16
    @6
    @28
    @18
    cconcat
    co
    @17
    @1
    @2
    @3
    @4
    @4
    @5
    df-s6
    eqtri
    vdegp1ci
    1p1e2
    eqtri
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsbergvtx
    @75
    @76
    cG
    ciedg
    cfv
    @19
    @20
    cE
    cG
    cV
    konigsberg.v
    konigsberg.e
    konigsberg.g
    konigsbergiedg
    @23
    eqtri
    vdegp1ci
    2p1e3
    eqtri
end
