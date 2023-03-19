include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wal.mm"
include "ccnv.mm"
include "cin.mm"
include "wrel.mm"
include "cdm.mm"
include "wceq.mm"
include "wer.mm"
include "wss.mm"
include "inss2.mm"
include "relcnv.mm"
include "relss.mm"
include "mp2.mm"
include "a1i.mm"
include "eqidd.mm"
include "brin.mm"
include "vex.mm"
include "brcnv.mm"
include "anbi2i.mm"
include "bitri.mm"
include "anbi12i.mm"
include "weq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "2albidv.mm"
include "spv.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "albidv.mm"
include "anbi2d.mm"
include "pm3.3.mm"
include "com23.mm"
include "adantrd.mm"
include "impd.mm"
include "4syl.mm"
include "adantld.mm"
include "jcad.mm"
include "bitr2i.mm"
include "syl6ib.mm"
include "syl5bi.mm"
include "bicomi.mm"
include "anbi12ci.mm"
include "3bitr4i.mm"
include "biimpi.mm"
include "jctil.mm"
include "alrimiv.mm"
include "alrimivv.mm"
include "dfer2.mm"
include "syl3anbrc.mm"

theorem trer
  let c.le: class .<_
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t

  disjoint a b
  disjoint a c
  disjoint .<_ a
  disjoint b c
  disjoint .<_ b
  disjoint .<_ c
  disjoint a r
  disjoint a s
  disjoint a t
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint c r
  disjoint c s
  disjoint c t
  disjoint r s
  disjoint r t
  disjoint .<_ r
  disjoint s t
  disjoint .<_ s
  disjoint .<_ t
  assert |- ( A. a A. b A. c ( ( a .<_ b /\ b .<_ c ) -> a .<_ c ) -> ( .<_ i^i `' .<_ ) Er dom ( .<_ i^i `' .<_ ) )

  proof
    va
    cv
    #
    vb
    cv
    #
    c.le
    wbr
    #
    @1
    vc
    cv
    #
    c.le
    wbr
    #
    wa
    #
    @0
    @3
    c.le
    wbr
    #
    wi
    #
    vc
    wal
    vb
    wal
    #
    va
    wal
    #
    c.le
    c.le
    ccnv
    #
    cin
    #
    wrel
    #
    @11
    cdm
    #
    @13
    wceq
    vr
    cv
    #
    vs
    cv
    #
    @11
    wbr
    #
    @15
    @14
    @11
    wbr
    #
    wi
    #
    @16
    @15
    vt
    cv
    #
    @11
    wbr
    #
    wa
    #
    @14
    @19
    @11
    wbr
    #
    wi
    #
    wa
    #
    vt
    wal
    #
    vs
    wal
    vr
    wal
    @13
    @11
    wer
    @12
    @9
    @11
    @10
    wss
    @10
    wrel
    @12
    c.le
    @10
    inss2
    c.le
    relcnv
    @11
    @10
    relss
    mp2
    a1i
    @9
    @13
    eqidd
    @9
    @25
    vr
    vs
    @9
    @24
    vt
    @9
    @23
    @18
    @21
    @14
    @15
    c.le
    wbr
    #
    @15
    @14
    c.le
    wbr
    #
    wa
    #
    @15
    @19
    c.le
    wbr
    #
    @19
    @15
    c.le
    wbr
    #
    wa
    #
    wa
    #
    @9
    @22
    @16
    @28
    @20
    @31
    @16
    @26
    @14
    @15
    @10
    wbr
    #
    wa
    #
    @28
    @14
    @15
    c.le
    @10
    brin
    #
    @33
    @27
    @26
    @14
    @15
    c.le
    vr
    vex
    #
    vs
    vex
    #
    brcnv
    #
    anbi2i
    bitri
    @20
    @29
    @15
    @19
    @10
    wbr
    #
    wa
    @31
    @15
    @19
    c.le
    @10
    brin
    @39
    @30
    @29
    @15
    @19
    c.le
    @37
    vt
    vex
    #
    brcnv
    anbi2i
    bitri
    anbi12i
    @9
    @32
    @14
    @19
    c.le
    wbr
    #
    @19
    @14
    c.le
    wbr
    #
    wa
    #
    @22
    @9
    @32
    @41
    @42
    @9
    @14
    @1
    c.le
    wbr
    #
    @4
    wa
    #
    @14
    @3
    c.le
    wbr
    #
    wi
    #
    vc
    wal
    #
    vb
    wal
    #
    @26
    @15
    @3
    c.le
    wbr
    #
    wa
    #
    @46
    wi
    #
    vc
    wal
    #
    @26
    @29
    wa
    #
    @41
    wi
    #
    @32
    @41
    wi
    @8
    @49
    va
    vr
    va
    vr
    weq
    #
    @7
    @47
    vb
    vc
    @56
    @5
    @45
    @6
    @46
    @56
    @2
    @44
    @4
    @0
    @14
    @1
    c.le
    breq1
    anbi1d
    @0
    @14
    @3
    c.le
    breq1
    imbi12d
    2albidv
    spv
    @48
    @53
    vb
    vs
    vb
    vs
    weq
    #
    @47
    @52
    vc
    @57
    @45
    @51
    @46
    @57
    @44
    @26
    @4
    @50
    @1
    @15
    @14
    c.le
    breq2
    @1
    @15
    @3
    c.le
    breq1
    #
    anbi12d
    imbi1d
    albidv
    spv
    @52
    @55
    vc
    vt
    vc
    vt
    weq
    #
    @51
    @54
    @46
    @41
    @59
    @50
    @29
    @26
    @3
    @19
    @15
    c.le
    breq2
    anbi2d
    @3
    @19
    @14
    c.le
    breq2
    imbi12d
    spv
    @55
    @28
    @31
    @41
    @55
    @26
    @31
    @41
    wi
    @27
    @55
    @31
    @26
    @41
    @55
    @29
    @26
    @41
    wi
    @30
    @55
    @26
    @29
    @41
    @26
    @29
    @41
    pm3.3
    com23
    adantrd
    com23
    adantrd
    impd
    4syl
    @9
    @19
    @1
    c.le
    wbr
    #
    @4
    wa
    #
    @19
    @3
    c.le
    wbr
    #
    wi
    #
    vc
    wal
    #
    vb
    wal
    #
    @30
    @50
    wa
    #
    @62
    wi
    #
    vc
    wal
    #
    @30
    @27
    wa
    #
    @42
    wi
    #
    @32
    @42
    wi
    @8
    @65
    va
    vt
    va
    vt
    weq
    #
    @7
    @63
    vb
    vc
    @71
    @5
    @61
    @6
    @62
    @71
    @2
    @60
    @4
    @0
    @19
    @1
    c.le
    breq1
    anbi1d
    @0
    @19
    @3
    c.le
    breq1
    imbi12d
    2albidv
    spv
    @64
    @68
    vb
    vs
    @57
    @63
    @67
    vc
    @57
    @61
    @66
    @62
    @57
    @60
    @30
    @4
    @50
    @1
    @15
    @19
    c.le
    breq2
    @58
    anbi12d
    imbi1d
    albidv
    spv
    @67
    @70
    vc
    vr
    vc
    vr
    weq
    #
    @66
    @69
    @62
    @42
    @72
    @50
    @27
    @30
    @3
    @14
    @15
    c.le
    breq2
    anbi2d
    @3
    @14
    @19
    c.le
    breq2
    imbi12d
    spv
    @70
    @28
    @31
    @42
    @70
    @27
    @31
    @42
    wi
    @26
    @70
    @31
    @27
    @42
    @70
    @30
    @27
    @42
    wi
    @29
    @30
    @27
    @42
    pm3.3
    adantld
    com23
    adantld
    impd
    4syl
    jcad
    @22
    @41
    @14
    @19
    @10
    wbr
    #
    wa
    @43
    @14
    @19
    c.le
    @10
    brin
    @73
    @42
    @41
    @14
    @19
    c.le
    @36
    @40
    brcnv
    anbi2i
    bitr2i
    syl6ib
    syl5bi
    @16
    @17
    @34
    @27
    @15
    @14
    @10
    wbr
    #
    wa
    @16
    @17
    @26
    @74
    @33
    @27
    @74
    @26
    @15
    @14
    c.le
    @37
    @36
    brcnv
    bicomi
    @38
    anbi12ci
    @35
    @15
    @14
    c.le
    @10
    brin
    3bitr4i
    biimpi
    jctil
    alrimiv
    alrimivv
    vr
    vs
    vt
    @13
    @11
    dfer2
    syl3anbrc
end
