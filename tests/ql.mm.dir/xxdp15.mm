include "wo.mm"
include "wa.mm"
include "lor.mm"
include "lan.mm"
include "tr.mm"
include "ran.mm"
include "wt.mm"
include "le1.mm"
include "leran.mm"
include "lelor.mm"
include "an1r.mm"
include "orass.mm"
include "cm.mm"
include "oridm.mm"
include "ror.mm"
include "orcom.mm"
include "3tr.mm"
include "lea.mm"
include "mlduali.mm"
include "lear.mm"
include "leror.mm"
include "bltr.mm"
include "or32.mm"
include "lbtr.mm"
include "letr.mm"
include "ax-arg.mm"
include "2an.mm"
include "2or.mm"
include "le3tr2.mm"
include "or12.mm"
include "orabs.mm"
include "ax-a2.mm"
include "ml3le.mm"
include "lelan.mm"
include "leao1.mm"
include "mldual2i.mm"
include "ancom.mm"
include "3tr2.mm"
include "bile.mm"
include "le2or.mm"

theorem xxdp15
  let wvd: term d
  let wve: term e
  let wvp: term p
  let wva0: term a0
  let wva1: term a1
  let wva2: term a2
  let wvb0: term b0
  let wvb1: term b1
  let wvb2: term b2
  let wvc0: term c0
  let wvc1: term c1
  let wvc2: term c2
  let wvp0: term p0
  let wvp2: term p2
  assume xxdp.1: |- p2 =< ( a2 v b2 )
  assume xxdp.c0: |- c0 = ( ( a1 v a2 ) ^ ( b1 v b2 ) )
  assume xxdp.c1: |- c1 = ( ( a0 v a2 ) ^ ( b0 v b2 ) )
  assume xxdp.c2: |- c2 = ( ( a0 v a1 ) ^ ( b0 v b1 ) )
  assume xxdp.d: |- d = ( a2 v ( a0 ^ ( a1 v b1 ) ) )
  assume xxdp.e: |- e = ( b0 ^ ( a0 v p0 ) )
  assume xxdp.p: |- p = ( ( ( a0 v b0 ) ^ ( a1 v b1 ) ) ^ ( a2 v b2 ) )
  assume xxdp.p0: |- p0 = ( ( a1 v b1 ) ^ ( a2 v b2 ) )
  assume xxdp.p2: |- p2 = ( ( a0 v b0 ) ^ ( a1 v b1 ) )


  assert |- ( ( a0 v a1 ) ^ ( ( b0 ^ ( a0 v p0 ) ) v b1 ) ) =< ( ( c0 v c1 ) v ( b1 ^ ( a0 v a1 ) ) )

  proof
    wva0
    wva1
    wo
    #
    wvb0
    wva0
    wvp0
    wo
    #
    wa
    #
    wvb1
    wo
    #
    wa
    #
    wva1
    wva2
    wo
    #
    wvb1
    wvb2
    wo
    #
    wa
    #
    wva0
    wva2
    wo
    #
    wvb0
    wvb2
    wo
    #
    wa
    #
    wvb1
    @0
    wa
    #
    wo
    #
    wo
    #
    wvc0
    wvc1
    wo
    @11
    wo
    #
    @4
    @8
    @2
    wvb2
    wo
    #
    wa
    #
    @5
    @11
    wo
    #
    @6
    wa
    #
    wo
    #
    @13
    @4
    @16
    @5
    wva0
    wva1
    wvb1
    wo
    #
    wa
    #
    wo
    #
    @6
    wa
    #
    wo
    #
    @19
    @4
    wva0
    wva2
    @21
    wo
    #
    wo
    #
    @15
    wa
    #
    wva1
    @25
    wo
    #
    @6
    wa
    #
    wo
    #
    @24
    @0
    wve
    wvb1
    wo
    #
    wa
    wva0
    wvd
    wo
    #
    wve
    wvb2
    wo
    #
    wa
    #
    wva1
    wvd
    wo
    #
    @6
    wa
    #
    wo
    @4
    @30
    wva0
    wva1
    wvd
    wve
    wvb1
    wvb2
    wva0
    wve
    wo
    #
    @20
    wa
    wva0
    wvb0
    wva0
    @20
    wva2
    wvb2
    wo
    #
    wa
    #
    wo
    #
    wa
    #
    wo
    #
    @20
    wa
    #
    wvd
    wvb2
    wo
    #
    @37
    @42
    @20
    wve
    @41
    wva0
    wve
    @2
    @41
    xxdp.e
    @1
    @40
    wvb0
    wvp0
    @39
    wva0
    xxdp.p0
    lor
    lan
    tr
    lor
    ran
    @43
    wva0
    wt
    @40
    wa
    #
    wo
    #
    @20
    wa
    #
    @44
    @42
    @46
    @20
    @41
    @45
    wva0
    wvb0
    wt
    @40
    wvb0
    le1
    leran
    lelor
    leran
    @47
    @38
    @21
    wo
    #
    @44
    @47
    @39
    @21
    wo
    #
    @48
    @47
    @39
    wva0
    wo
    #
    @20
    wa
    @49
    @46
    @50
    @20
    @46
    wva0
    @40
    wo
    #
    wva0
    wva0
    wo
    #
    @39
    wo
    #
    @50
    @45
    @40
    wva0
    @40
    an1r
    lor
    @53
    @51
    wva0
    wva0
    @39
    orass
    cm
    @53
    @40
    @50
    @52
    wva0
    @39
    wva0
    oridm
    ror
    wva0
    @39
    orcom
    tr
    3tr
    ran
    @39
    wva0
    @20
    @20
    @38
    lea
    mlduali
    tr
    @39
    @38
    @21
    @20
    @38
    lear
    leror
    bltr
    @48
    @25
    wvb2
    wo
    #
    @44
    wva2
    wvb2
    @21
    or32
    @44
    @54
    wvd
    @25
    wvb2
    xxdp.d
    ror
    cm
    tr
    lbtr
    letr
    bltr
    ax-arg
    @31
    @3
    @0
    wve
    @2
    wvb1
    xxdp.e
    ror
    lan
    @34
    @27
    @36
    @29
    @32
    @26
    @33
    @15
    wvd
    @25
    wva0
    xxdp.d
    lor
    wve
    @2
    wvb2
    xxdp.e
    ror
    2an
    @35
    @28
    @6
    wvd
    @25
    wva1
    xxdp.d
    lor
    ran
    2or
    le3tr2
    @27
    @16
    @29
    @23
    @26
    @8
    @15
    @26
    wva2
    wva0
    @21
    wo
    #
    wo
    wva2
    wva0
    wo
    @8
    wva0
    wva2
    @21
    or12
    @55
    wva0
    wva2
    wva0
    @20
    orabs
    lor
    wva2
    wva0
    orcom
    3tr
    ran
    @23
    @29
    @22
    @28
    @6
    wva1
    wva2
    @21
    orass
    ran
    cm
    2or
    lbtr
    @23
    @18
    @16
    @22
    @17
    @6
    @22
    wva2
    wva1
    @11
    wo
    #
    wo
    #
    @17
    @22
    wva2
    wva1
    wva0
    wvb1
    wva1
    wo
    #
    wa
    #
    wo
    #
    wo
    #
    @57
    @22
    wva2
    wva1
    wo
    #
    @59
    wo
    @61
    @5
    @62
    @21
    @59
    wva1
    wva2
    ax-a2
    @20
    @58
    wva0
    wva1
    wvb1
    ax-a2
    lan
    2or
    wva2
    wva1
    @59
    orass
    tr
    @60
    @56
    wva2
    wva1
    wva0
    wvb1
    ml3le
    lelor
    bltr
    @57
    @62
    @11
    wo
    #
    @17
    @63
    @57
    wva2
    wva1
    @11
    orass
    cm
    @62
    @5
    @11
    wva2
    wva1
    ax-a2
    ror
    tr
    lbtr
    leran
    lelor
    letr
    @19
    @10
    @7
    @11
    wo
    #
    wo
    @13
    @16
    @10
    @18
    @64
    @15
    @9
    @8
    @2
    wvb0
    wvb2
    wvb0
    @1
    lea
    leror
    lelan
    @18
    @64
    @6
    @17
    wa
    @6
    @5
    wa
    #
    @11
    wo
    @18
    @64
    @11
    @5
    @6
    wvb1
    @0
    wvb2
    leao1
    mldual2i
    @6
    @17
    ancom
    @65
    @7
    @11
    @6
    @5
    ancom
    ror
    3tr2
    bile
    le2or
    @10
    @7
    @11
    or12
    lbtr
    letr
    @13
    wvc0
    wvc1
    @11
    wo
    #
    wo
    #
    @14
    @67
    @13
    wvc0
    @7
    @66
    @12
    xxdp.c0
    wvc1
    @10
    @11
    xxdp.c1
    ror
    2or
    cm
    @14
    @67
    wvc0
    wvc1
    @11
    orass
    cm
    tr
    lbtr
end
